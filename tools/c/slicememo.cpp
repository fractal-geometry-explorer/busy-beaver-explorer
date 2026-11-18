// slicememo: an exact accelerated simulator for 2-symbol Turing machines from blank tape, in the style of the
// layered rule memo that DeepMind's busycoq PRs 88 and 91 certify ("hashlife along the tape").
//
// The tape is  [left stack] [window W] [right stack].  A stack node is
//   SLICE(parent, up to 64 cells)  -- the parent is everything further out,
//   WALL(phase)                    -- inner->outer  j0 w0^c0 j1 w1^c1 ... j_k 0^inf : junk words j_i and crystal words
//                                     w_i whose repeat counts c_i (at most K=4) are NOT part of the node: they are kept
//                                     as numbers outside the memo, so a wall that grows on every visit keeps its id,
//   BLANK (node 0)                 -- zeros forever.
// rule(side, node, q): the head enters the node at its inner edge in state q; it runs until it leaves it inward.
// The result is memoized per (node, q): the new node, the exit state, the steps A + sum B_i c_i, the new counts
// c'_i = c_{src_i} + d_i, and lower bounds lb_i the counts must meet for the result to hold.  A slice's rule is
// evaluated by stepping the slice and calling the parent's rule whenever the head leaves outward, so a rule of a
// high slice reuses the rules below it.  A wall's rule is computed symbolically: a crystal is crossed at once when the
// head comes out of one word on the far side in the state it entered (steps linear in the count); otherwise the
// crossing is re-bracketed one word at a time (count - 1, recorded in lb).  When a memoized result needs more
// copies than a crystal has, the call is redone with the actual counts (ruleC), which lets a crystal run out.
// Everything is exact; with -DEXACT the step counts and crystal counts are 128-bit integers, otherwise doubles.
//
// usage: slicememo TM T0 WALL FIXn ITERCAP [MINRUNCELLS]
//   T0     steps of plain simulation first (then, with a wall, until the head is at the far end from it)
//   WALL   L, R or N: which end of the tape is a crystal wall
//   FIXn   slice width n cells (8..64)
//   output one line: TM RESULT ... steps=... (RESULT: HALT, STALL:<why>, NORET (head never comes back), lb, topcap)
//   env: STOPAT=s  print "SNAP steps headoffset state tape" at the first top-level point with steps >= s, and stop
//        MINW=n   crystal words at least n cells (a power of the primitive period); RUNT, MAXP: crystal detection;
//        WMAX     window size; WALLS=1 lists the wall phases met
#include <bits/stdc++.h>
#include "tm.h"
using namespace std;
#ifdef EXACT
typedef __int128 num; const num NEG=-((num)1<<120);
static string numstr(num v){ if(v==0) return "0"; bool neg=v<0; if(neg) v=-v; string s; while(v>0){ s+=char('0'+(int)(v%10)); v/=10; } if(neg) s+='-'; reverse(s.begin(),s.end()); return s; }
static double numd(num v){ return (double)v; }
#else
typedef double num; const num NEG=-1e300;
static string numstr(num v){ char b[64]; snprintf(b,64,"%.10e",v); return b; }
static double numd(num v){ return v; }
#endif
const int K=4; const int NSM=6;
int NS; int TW[8][2], TMV[8][2], TN[8][2];
const uint32_t UNK=0xFFFFFFFF, HALT=0xFFFFFFFE, NORET=0xFFFFFFFD, STALL=0xFFFFFFFC, INPROG=0xFFFFFFFB, FAIL=0xFFFFFFFA;

struct Res{ uint32_t n; uint8_t q; int8_t src[K]; num A; num B[K]; num d[K]; num lb[K]; };
static Res mkres(uint32_t n){ Res r; r.n=n; r.q=0; r.A=0; for(int i=0;i<K;i++){r.src[i]=i; r.B[i]=0; r.d[i]=0; r.lb[i]=NEG;} return r; }
// apply child result r (expressed in current counts) on top of accumulator acc (entry -> current)
static bool compose(Res &acc, const Res &r){
  for(int j=0;j<K;j++){ if(r.lb[j]<=NEG/2) continue; if(acc.src[j]>=0) acc.lb[acc.src[j]]=max(acc.lb[acc.src[j]], r.lb[j]-acc.d[j]); else if(acc.d[j]<r.lb[j]) return false; }
  acc.A+=r.A; for(int j=0;j<K;j++){ if(r.B[j]==0) continue; acc.A+=r.B[j]*acc.d[j]; if(acc.src[j]>=0) acc.B[acc.src[j]]+=r.B[j]; }
  int8_t ns[K]; num nd[K];
  for(int i=0;i<K;i++){ int s=r.src[i]; if(s>=0){ ns[i]=acc.src[s]; nd[i]=r.d[i]+acc.d[s]; } else { ns[i]=-1; nd[i]=r.d[i]; } }
  for(int i=0;i<K;i++){ acc.src[i]=ns[i]; acc.d[i]=nd[i]; }
  acc.n=r.n; acc.q=r.q; return true;
}
struct WallPh{ vector<string> j, w; };
static string wkey(const WallPh&p){ string s; for(size_t i=0;i<p.w.size();i++) s+=p.j[i]+"|"+p.w[i]+"|"; s+=p.j.back(); return s; }
static inline uint64_t mix(uint64_t x){ x^=x>>31; x*=0x7fb5d329728ea185ULL; x^=x>>27; x*=0x81dadef4bc2dd44dULL; x^=x>>33; return x; }
struct Key{ uint32_t p; uint8_t len; uint64_t s; bool operator==(const Key&o)const{return p==o.p&&len==o.len&&s==o.s;} };
struct KH{ size_t operator()(const Key&k)const{ return mix(k.s ^ mix(((uint64_t)k.p<<8)|k.len)); } };
struct Side {
  vector<uint32_t> par; vector<uint64_t> sl; vector<uint8_t> kind, len; vector<array<int32_t,NSM>> mi;
  unordered_map<Key,uint32_t,KH> h; vector<Res> memo;
  vector<WallPh> walls; unordered_map<string,uint32_t> wh; bool blank=true;
  void reset(){ par.clear(); sl.clear(); kind.clear(); len.clear(); mi.clear(); h.clear(); memo.clear(); walls.clear(); wh.clear();
    newnode(0,0,0,0); }
  Side(){ reset(); }
  uint32_t newnode(uint32_t p, uint64_t s, int k, int l){ uint32_t id=par.size(); par.push_back(p); sl.push_back(s); kind.push_back(k); len.push_back(l); array<int32_t,NSM> a; a.fill(-1); mi.push_back(a); return id; }
  uint32_t mk(uint32_t p, uint64_t s, int l){
    if(blank && p==0 && s==0) return 0;
    Key k{p,(uint8_t)l,s}; auto it=h.find(k); if(it!=h.end()) return it->second;
    uint32_t id=newnode(p,s,0,l); h[k]=id; return id;
  }
  uint32_t mkwall(const WallPh&w){ string key=wkey(w); auto it=wh.find(key); if(it!=wh.end()) return it->second;
    uint32_t wid=walls.size(); walls.push_back(w); uint32_t id=newnode(0,wid,1,0); wh[key]=id; return id; }
} SD[2];
long long iterCap=2000000000LL, totalIters=0, ruleCalls=0, ruleMiss=0, wallMiss=0; int depth=0, maxDepth=0; string failWhy;
int BLANKLEN=16, RUNT=6, MAXP=12, MINW=1;
int outwardMove(int side,int mv){ return side==0 ? (mv==-1) : (mv==1); }
int crossBlock(int side, string &u, int &s, long long &t, bool fromInner){
  int p=u.size(); int pos= fromInner?0:p-1; t=0;
  for(int it=0; it<100000; it++){
    int b=u[pos]-'0'; int nx=TN[s][b]; if(nx<0) return -1;
    u[pos]='0'+TW[s][b]; int mv=TMV[s][b]; s=nx; t++;
    if(outwardMove(side,mv)) pos++; else pos--;
    if(pos>=p) return fromInner?1:0;
    if(pos<0) return fromInner?0:1;
  }
  return -2;
}
// find a run of >= RUNT copies of a word of period <= MAXP inside s; returns (start, period, copies) of the longest (in cells)
static bool findRun(const string&s, int &st, int &p, int &k){
  int n=s.size(); int bestCells=0;
  for(int pp=1; pp<=MAXP; pp++){ int run=0;
    for(int i=pp;i<=n;i++){ if(i<n && s[i]==s[i-pp]){ run++; continue; }
      int cells=run+pp; int mult=(MINW+pp-1)/pp; int P=pp*mult; int kk=cells/P; if(kk>=RUNT && kk*P>bestCells){ bestCells=kk*P; st=i-cells; p=P; k=kk; } run=0; }
  }
  return bestCells>0;
}
// canonicalize a wall: absorb copies, shift runs inward, dissolve tiny constant runs, detect new runs
struct RunSym{ int src; num d; };
static void canon(WallPh &w, vector<RunSym> &rs){
  bool changed=true; int guard=0;
  while(changed && guard++<1000){ changed=false;
    for(size_t i=0;i<w.w.size();i++){ string &u=w.w[i]; int p=u.size(); string &a=w.j[i]; string &b=w.j[i+1];
      while((int)a.size()>=p && a.compare(a.size()-p,p,u)==0){ a.resize(a.size()-p); rs[i].d+=1; changed=true; }
      while(!a.empty() && a.back()==u.back()){ char z=u.back(); b=string(1,z)+b; u=string(1,z)+u.substr(0,p-1); a.pop_back(); changed=true;
        while((int)a.size()>=p && a.compare(a.size()-p,p,u)==0){ a.resize(a.size()-p); rs[i].d+=1; } }
      while((int)b.size()>=p && b.compare(0,p,u)==0){ b=b.substr(p); rs[i].d+=1; changed=true; }
    }
    for(size_t i=0;i<w.w.size();i++) if(rs[i].src<0 && rs[i].d<=2){ string mid; for(long long k=0;k<(long long)rs[i].d;k++) mid+=w.w[i];
        w.j[i]=w.j[i]+mid+w.j[i+1]; w.j.erase(w.j.begin()+i+1); w.w.erase(w.w.begin()+i); rs.erase(rs.begin()+i); changed=true; break; }
    if(changed) continue;
    if((int)w.w.size()<K) for(size_t i=0;i<w.j.size();i++){ int st,p,k; if(findRun(w.j[i],st,p,k)){
        string a=w.j[i].substr(0,st), u=w.j[i].substr(st,p), b=w.j[i].substr(st+p*k);
        w.j[i]=a; w.j.insert(w.j.begin()+i+1,b); w.w.insert(w.w.begin()+i,u); rs.insert(rs.begin()+i,RunSym{-1,(num)k}); changed=true; break; } }
  }
  while(!w.j.back().empty() && w.j.back().back()=='0') w.j.back().pop_back();
}
Res wallRule(int side, uint32_t id, int q, const num* cc=nullptr){
  Side &D=SD[side]; WallPh w=D.walls[D.sl[id]]; wallMiss++;
  int nr=w.w.size(); vector<RunSym> rs(nr); for(int i=0;i<nr;i++) rs[i]= cc? RunSym{-1,cc[i]} : RunSym{i,0};
  Res acc=mkres(0); // we build A,B,lb here; src/d filled at the end
  int seg=0, pos=0, st=q; long long guard=0; int rots=0;
  auto bad=[&](const char*why)->Res{ failWhy=why; Res r=mkres(STALL); return r; };
  while(true){
    if(++guard>20000000) return bad("wall guard");
    string &J=w.j[seg];
    if(pos<0){ if(seg==0) break; // exit inward
      int i=seg-1; // enter run i from outer side
      if(rs[i].src<0 && rs[i].d<=2){ string mid; for(long long k=0;k<(long long)rs[i].d;k++) mid+=w.w[i]; int off=w.j[i].size()+mid.size();
        w.j[i]=w.j[i]+mid+w.j[i+1]; w.j.erase(w.j.begin()+i+1); w.w.erase(w.w.begin()+i); rs.erase(rs.begin()+i); seg=i; pos=off-1; continue; }
      string u2=w.w[i]; int s2=st; long long t; int r=crossBlock(side,u2,s2,t,false);
      if(r==-1||r==-2) return bad("halt/loop in block");
      if(r==1 && s2==st){ w.w[i]=u2; acc.A+=t*rs[i].d; if(rs[i].src>=0) acc.B[rs[i].src]+=t; seg=i; pos=w.j[i].size()-1; continue; }
      if(++rots>8*(int)w.w[i].size()) return bad("rotations");
      { string &u=w.w[i]; char x=u.back(); string a=u.substr(0,u.size()-1); w.j[i]+=a; u=string(1,x)+a; rs[i].d-=1;
        if(rs[i].src>=0) acc.lb[rs[i].src]=max(acc.lb[rs[i].src], -rs[i].d); else if(rs[i].d<0) return bad("const run underflow");
        w.j[i+1]=string(1,x)+w.j[i+1]; seg=i+1; pos=0; }
      continue;
    }
    if(pos>=(int)J.size()){
      if(seg==(int)w.w.size()){ J+='0'; if(J.size()>200000) return bad("wall junk grows"); }
      else { int i=seg; // enter run i from inner side
        if(rs[i].src<0 && rs[i].d<=2){ string mid; for(long long k=0;k<(long long)rs[i].d;k++) mid+=w.w[i]; int off=w.j[i].size();
          w.j[i]=w.j[i]+mid+w.j[i+1]; w.j.erase(w.j.begin()+i+1); w.w.erase(w.w.begin()+i); rs.erase(rs.begin()+i); pos=off; continue; }
        string u2=w.w[i]; int s2=st; long long t; int r=crossBlock(side,u2,s2,t,true);
        if(r==-1||r==-2) return bad("halt/loop in block");
        if(r==1 && s2==st){ w.w[i]=u2; acc.A+=t*rs[i].d; if(rs[i].src>=0) acc.B[rs[i].src]+=t; seg=i+1; pos=0; continue; }
        if(++rots>8*(int)w.w[i].size()) return bad("rotations");
        { string &u=w.w[i]; char y=u[0]; string b=u.substr(1); w.j[i]+=y; u=b+y; rs[i].d-=1;
          if(rs[i].src>=0) acc.lb[rs[i].src]=max(acc.lb[rs[i].src], -rs[i].d); else if(rs[i].d<0) return bad("const run underflow");
          w.j[i+1]=b+w.j[i+1]; pos=w.j[i].size()-1; }
        continue; }
    }
    string &JJ=w.j[seg];
    int b=JJ[pos]-'0'; int nx=TN[st][b]; if(nx<0){ Res r=acc; r.n=HALT; r.q=st; r.A+=1; return r; }
    JJ[pos]='0'+TW[st][b]; int mv=TMV[st][b]; st=nx; acc.A+=1;
    if(outwardMove(side,mv)) pos++; else pos--;
  }
  canon(w,rs);
  if((int)w.w.size()>K) return bad("too many runs");
  Res r=acc; r.n=D.mkwall(w); r.q=st;
  for(int i=0;i<K;i++){ if(i<(int)rs.size()){ r.src[i]=rs[i].src; r.d[i]=rs[i].d; } else { r.src[i]=-1; r.d[i]=0; } }
  return r;
}
Res rule(int side, uint32_t id, int q){
  Side &D=SD[side]; ruleCalls++;
  int32_t mx=D.mi[id][q];
  if(mx==-2){ Res r=mkres(NORET); return r; }
  if(mx>=0) return D.memo[mx];
  ruleMiss++;
  Res out;
  if(D.kind[id]==1){ out=wallRule(side,id,q); if(out.n!=STALL){ D.mi[id][q]=D.memo.size(); D.memo.push_back(out);} return out; }
  D.mi[id][q]=-2; depth++; if(depth>maxDepth) maxDepth=depth;
  uint32_t p=D.par[id]; uint64_t s=D.sl[id]; int L= id==0? BLANKLEN : D.len[id]; int pos=0, st=q;
  Res acc=mkres(0);
  int inw = side==0 ? 1 : -1;
  uint32_t bp=p; uint64_t bs=s; int bpos=pos, bst=st; Res bacc=acc; long long lam=1, pw=1;
  while(true){
    int b=(s>>pos)&1; int nx=TN[st][b];
    if(nx<0){ out=acc; out.n=HALT; out.q=st; out.A+=1; break; }
    if(TW[st][b]) s|=(1ULL<<pos); else s&=~(1ULL<<pos);
    acc.A+=1; int mv=TMV[st][b]; st=nx;
    if(mv==inw){ pos--; if(pos<0){ out=acc; out.n=D.mk(p,s,L); out.q=st; break; } }
    else { pos++; if(pos==L){ Res r=rule(side,p,st);
        if(r.n>=FAIL && r.n!=INPROG){ if(r.n==HALT){ Res rr=r; rr.n=0; if(!compose(acc,rr)){ out=mkres(STALL); failWhy="lb"; break;} out=acc; out.n=HALT; out.q=r.q; } else out=r; break; }
        if(!compose(acc,r)){ out=mkres(STALL); failWhy="lb (const)"; break; }
        p=r.n; st=r.q; pos=L-1; } }
    if(++totalIters > iterCap){ out=mkres(STALL); failWhy="iterCap"; break; }
    if(p==bp && s==bs && pos==bpos && st==bst){ bool grow=true; for(int i=0;i<K;i++){ if(acc.src[i]!=bacc.src[i] || acc.d[i]<bacc.d[i]) grow=false; }
      out=acc; out.n= grow? NORET : STALL; if(!grow) failWhy="shrinking cycle"; break; }
    if(lam==pw){ bp=p;bs=s;bpos=pos;bst=st;bacc=acc; pw*=2; lam=0;} lam++;
  }
  depth--;
  if(out.n==STALL){ D.mi[id][q]=-1; return out; }
  D.mi[id][q]=D.memo.size(); D.memo.push_back(out);
  return out;
}
// concrete evaluation: counts c (current, absolute). Returns Res with src=-1, d = new counts, A = steps, no lb.
long long concCalls=0;
static Res concretize(const Res&r, const num*c){ Res o=r; num st=r.A; for(int i=0;i<K;i++) st+=r.B[i]*c[i];
  for(int i=0;i<K;i++){ o.d[i]=(r.src[i]>=0? c[r.src[i]]:0)+r.d[i]; o.src[i]=-1; o.B[i]=0; o.lb[i]=NEG; } o.A=st; return o; }
static bool lbOK(const Res&r,const num*c){ for(int i=0;i<K;i++) if(r.lb[i]>NEG/2 && c[i]<r.lb[i]) return false; return true; }
Res ruleC(int side, uint32_t id, int q, const num* c){
  Res r=rule(side,id,q);
  if(r.n==HALT){ if(lbOK(r,c)) return concretize(r,c); }
  else if(!(r.n>=FAIL && r.n!=INPROG) && lbOK(r,c)) return concretize(r,c);
  concCalls++;
  Side &D=SD[side];
  if(D.kind[id]==1){ Res w=wallRule(side,id,q,c); if(w.n>=FAIL && w.n!=INPROG && w.n!=HALT) return w; return concretize(w,c); }
  uint32_t p=D.par[id]; uint64_t s=D.sl[id]; int L= id==0? BLANKLEN : D.len[id]; int pos=0, st=q;
  num cur[K]; for(int i=0;i<K;i++) cur[i]=c[i]; num A=0; int inw = side==0 ? 1 : -1; long long it=0;
  Res out=mkres(0);
  while(true){
    int b=(s>>pos)&1; int nx=TN[st][b];
    if(nx<0){ out.n=HALT; out.q=st; A+=1; break; }
    if(TW[st][b]) s|=(1ULL<<pos); else s&=~(1ULL<<pos);
    A+=1; int mv=TMV[st][b]; st=nx;
    if(mv==inw){ pos--; if(pos<0){ out.n=D.mk(p,s,L); out.q=st; break; } }
    else { pos++; if(pos==L){ Res r2=ruleC(side,p,st,cur);
        if(r2.n>=FAIL && r2.n!=INPROG){ if(r2.n==HALT){ A+=r2.A; out.n=HALT; out.q=r2.q; } else { out=r2; return out; } break; }
        A+=r2.A; for(int i=0;i<K;i++) cur[i]=r2.d[i]; p=r2.n; st=r2.q; pos=L-1; } }
    if(++it>100000000){ failWhy="conc cap"; return mkres(STALL); }
  }
  out.A=A; for(int i=0;i<K;i++){ out.src[i]=-1; out.d[i]=cur[i]; out.B[i]=0; out.lb[i]=NEG; }
  return out;
}
string SEP=""; int MN=8, MX=32, FIX=16;
vector<string> chunk(const string& cells, bool fromLeft){
  vector<string> out; int n=cells.size();
  if(fromLeft){ for(int i=0;i<n;i+=FIX) out.push_back(cells.substr(i,min(FIX,n-i))); }
  else { int r=n%FIX; if(r) out.push_back(cells.substr(0,r)); for(int i=r;i<n;i+=FIX) out.push_back(cells.substr(i,FIX)); }
  return out;
}
uint64_t packInner(const string& c, int side){ uint64_t s=0; int n=c.size(); for(int j=0;j<n;j++){ int ci= side==0? n-1-j : j; if(c[ci]=='1') s|=1ULL<<j; } return s; }
string unpack(uint64_t s,int n,int side){ string c(n,'0'); for(int j=0;j<n;j++) if(s>>j&1){ int idx= side==0? n-1-j : j; c[idx]='1'; } return c; }
uint32_t buildStack(int side, uint32_t base, const string& cells){
  vector<string> ch = chunk(cells, side==0); uint32_t cur=base;
  if(side==0){ for(size_t k=0;k<ch.size();k++) cur=SD[0].mk(cur,packInner(ch[k],0),ch[k].size()); }
  else { for(int k=(int)ch.size()-1;k>=0;k--) cur=SD[1].mk(cur,packInner(ch[k],1),ch[k].size()); }
  return cur;
}
string materialize(int side, uint32_t id, uint32_t &base){
  vector<string> parts; while(id!=0 && SD[side].kind[id]==0){ parts.push_back(unpack(SD[side].sl[id],SD[side].len[id],side)); id=SD[side].par[id]; }
  base=id; string out; if(side==0){ for(int k=parts.size()-1;k>=0;k--) out+=parts[k]; } else { for(auto&p:parts) out+=p; } return out; }
int WMAX=64; long long rebuilds=0;
// dissolve runs with small concrete counts into junk; returns new top node
uint32_t rebuildSide(int side, uint32_t top, vector<num>&c, num thr){
  uint32_t base; string cells=materialize(side,top,base);
  if(SD[side].kind[base]!=1) return top;
  WallPh w=SD[side].walls[SD[side].sl[base]]; vector<RunSym> rs;
  for(size_t i=0;i<w.w.size();i++) rs.push_back(RunSym{(int)i,0});
  for(int i=(int)w.w.size()-1;i>=0;i--) if(c[i]<thr){ string mid; for(long long k=0;k<(long long)c[i];k++) mid+=w.w[i];
      w.j[i]=w.j[i]+mid+w.j[i+1]; w.j.erase(w.j.begin()+i+1); w.w.erase(w.w.begin()+i); rs.erase(rs.begin()+i); }
  canon(w,rs);
  vector<num> nc(K,0); for(size_t i=0;i<rs.size() && i<(size_t)K;i++) nc[i]=(rs[i].src>=0? c[rs[i].src]:0)+rs[i].d;
  if((int)w.w.size()>K) return top;
  c=nc; uint32_t nb=SD[side].mkwall(w); rebuilds++;
  return buildStack(side,nb,cells);
}
int main(int argc,char**argv){
  if(argc<2){fprintf(stderr,"usage: mstk TM T0 wallside(L/R/N) fixN iterCap [minRunCells]\n");return 1;}
  string m=argv[1]; long long T0= argc>2? atoll(argv[2]) : 0;
  char wside= argc>3? argv[3][0] : 'N';
  string sp = argc>4? argv[4] : "fix16"; FIX=atoi(sp.c_str()+3);
  if(argc>5) iterCap=atoll(argv[5]);
  int minRunCells = argc>6? atoi(argv[6]) : 60;
  long long topCap=4000000000LL;
  if(getenv("WMAX")) WMAX=atoi(getenv("WMAX")); if(getenv("RUNT")) RUNT=atoi(getenv("RUNT")); if(getenv("MAXP")) MAXP=atoi(getenv("MAXP")); if(getenv("MINW")) MINW=atoi(getenv("MINW"));
  NS=(m.size()+1)/7;
  for(int s=0;s<NS;s++)for(int y=0;y<2;y++){const char*t=m.c_str()+7*s+3*y;
    if(t[2]=='-'||t[2]-'A'>=NS){TN[s][y]=-1;TW[s][y]=1;TMV[s][y]=1;continue;}
    TW[s][y]=t[0]-'0'; TMV[s][y]= t[1]=='R'?1:-1; TN[s][y]=t[2]-'A';}
  tm_machine tmm; tm_parse(m.c_str(),&tmm); tm_tape tp; tm_tape_init(&tp,1<<16); int st0=0;
  for(long long i=0;i<T0;i++){ if(!tm_step(&tmm,&tp,&st0)){ printf("%s HALT-raw steps=%lld\n",m.c_str(),i+1); return 0; } }
  long long extra=0;
  if(wside=='L'||wside=='R'){ while(true){ long long d = wside=='L' ? tp.hi-tp.head : tp.head-tp.lo; if(d<=4) break;
      if(!tm_step(&tmm,&tp,&st0)){ printf("%s HALT-raw\n",m.c_str()); return 0; } extra++; if(extra>300000000LL){printf("%s no-approach\n",m.c_str());return 0;} } }
  T0+=extra;
  long long lo=min(tp.lo,tp.head), hi=max(tp.hi,tp.head), hd=tp.head;
  auto cell=[&](long long x)->int{ return (x>=tp.lo && x<=tp.hi)? tp.c[x+tp.off] : 0; };
  long long w0,w1; if(wside=='L'){ w0=hd-8; w1=hi; } else if(wside=='R'){ w0=lo; w1=hd+8; } else { w0=hd-8; w1=hd+8; }
  string W; for(long long x=w0;x<=w1;x++) W+=char('0'+cell(x));
  vector<num> cW[2]={vector<num>(K,0),vector<num>(K,0)}; uint32_t LR[2]={0,0};
  for(int side=0; side<2; side++){
    bool wall = (side==0 && wside=='L') || (side==1 && wside=='R');
    string reg; if(side==0) for(long long x=min(lo,w0);x<w0;x++) reg+=char('0'+cell(x)); else for(long long x=w1+1;x<=max(hi,w1);x++) reg+=char('0'+cell(x));
    if(wall){
      SD[side].blank=false;
      string str=reg; if(side==0) reverse(str.begin(),str.end()); // inner->outer
      // wall region starts at the innermost long run
      int n=str.size(); int startW=n;
      for(int pp=1;pp<=MAXP && startW==n;pp++){} 
      { int best=n; for(int pp=1;pp<=MAXP;pp++){ int run=0; for(int i=pp;i<n;i++){ if(str[i]==str[i-pp]){ run++; if(run+pp>=minRunCells){ best=min(best,i-run-pp+1); break; } } else run=0; } } startW=best; }
      if(startW==n){ fprintf(stderr,"no run on wall side\n"); printf("%s no-wall-run\n",m.c_str()); return 0; }
      WallPh w; w.j.push_back(str.substr(startW)); vector<RunSym> rs; canon(w,rs);
      if(w.w.empty()){ printf("%s no-wall-run2\n",m.c_str()); return 0; }
      for(size_t i=0;i<rs.size();i++){ cW[side][i]=rs[i].d; }
      uint32_t base=SD[side].mkwall(w);
      string inner=str.substr(0,startW); if(side==0) reverse(inner.begin(),inner.end());
      fprintf(stderr,"side %d wall: %s counts:",side,wkey(w).substr(0,300).c_str()); for(size_t i=0;i<rs.size();i++) fprintf(stderr," %g",numd(rs[i].d)); fprintf(stderr," inner=%zu\n",inner.size());
      LR[side]=buildStack(side,base,inner);
    } else {
      if(side==0){ size_t f=reg.find('1'); reg = f==string::npos? "" : reg.substr(f); } else { size_t f=reg.find_last_of('1'); reg = f==string::npos? "" : reg.substr(0,f+1); }
      LR[side]=buildStack(side,0,reg);
    }
  }
  int pos=hd-w0, st=st0; num steps=T0; long long top=0, pushes=0;
  string why="topcap";
  auto lbok=[&](int side, Res &r)->bool{ for(int i=0;i<K;i++) if(r.lb[i]>NEG/2 && cW[side][i] < r.lb[i]) return false; return true; };
  auto applyTop=[&](int side, Res &r)->bool{ // returns false on failure
    for(int i=0;i<K;i++) if(r.lb[i]>NEG/2 && cW[side][i] < r.lb[i]){ why="lb"; return false; }
    steps+=r.A; for(int i=0;i<K;i++) steps+=r.B[i]*cW[side][i];
    vector<num> nc(K); for(int i=0;i<K;i++) nc[i]=(r.src[i]>=0? cW[side][r.src[i]]:0)+r.d[i]; cW[side]=nc; return true; };
  auto t0=chrono::steady_clock::now();
  num stopAt = getenv("STOPAT")? (num)atof(getenv("STOPAT")) : (num)-1;
  auto fullTape=[&](int side)->string{ uint32_t base; string cells=materialize(side,LR[side],base); string wall;
    if(SD[side].kind[base]==1){ WallPh w=SD[side].walls[SD[side].sl[base]]; string io; for(size_t i=0;i<w.w.size();i++){ io+=w.j[i]; for(long long k=0;k<(long long)cW[side][i];k++) io+=w.w[i]; } io+=w.j.back();
      if(side==0){ reverse(io.begin(),io.end()); } wall=io; }
    return side==0? wall+cells : cells+wall; };
  while(top++<topCap){
    if(stopAt>=0 && steps>=stopAt){ string l=fullTape(0), r=fullTape(1); string all=l+W+r; size_t hp=l.size()+pos;
      size_t f=all.find('1'); size_t e=all.find_last_of('1'); if(f==string::npos){f=hp;e=hp;} f=min(f,hp); e=max(e,hp);
      printf("SNAP %s %zu %d %s\n", numstr(steps).c_str(), hp-f, st, all.substr(f,e-f+1).c_str()); return 0; }
    int b=W[pos]-'0'; int nx=TN[st][b];
    if(nx<0){ why="HALT"; steps+=1; break; }
    W[pos]='0'+TW[st][b]; steps+=1; int mv=TMV[st][b]; st=nx; pos+=mv;
    if(pos==(int)W.size()){
      uint32_t R=LR[1];
      if(SD[1].blank && R==0){ if((int)W.size()<WMAX){ W+='0'; continue; }
        string c0=W.substr(0,FIX); LR[0]=SD[0].mk(LR[0],packInner(c0,0),c0.size()); W=W.substr(c0.size()); pos-=c0.size(); W+='0'; pushes++; continue; }
      if(SD[1].blank && SD[1].kind[R]==0 && SD[1].par[R]==0 && (int)W.size()+SD[1].len[R]<=WMAX){ W+=unpack(SD[1].sl[R],SD[1].len[R],1); LR[1]=0; continue; }
      Res r=rule(1,R,st);
      if((r.n>=FAIL && r.n!=INPROG) ? (r.n==HALT && !lbok(1,r)) || r.n==STALL : !lbok(1,r)){ r=ruleC(1,R,st,cW[1].data()); if(!(r.n>=FAIL && r.n!=INPROG) || r.n==HALT){ for(int i=0;i<K;i++) r.lb[i]=NEG; r.src[0]=-1; } }
      if(r.n>=FAIL && r.n!=INPROG){ if(r.n==HALT){ applyTop(1,r); why="HALT"; } else why= r.n==NORET?"NORET":"STALL:"+failWhy; break; }
      if(!applyTop(1,r)) break; st=r.q; LR[1]=r.n; pos=W.size()-1;
    } else if(pos<0){
      uint32_t L=LR[0];
      if(SD[0].blank && L==0){ if((int)W.size()<WMAX){ W='0'+W; pos=0; continue; }
        string c0=W.substr(W.size()-FIX); LR[1]=SD[1].mk(LR[1],packInner(c0,1),c0.size()); W=W.substr(0,W.size()-c0.size()); W='0'+W; pos=0; pushes++; continue; }
      if(SD[0].blank && SD[0].kind[L]==0 && SD[0].par[L]==0 && (int)W.size()+SD[0].len[L]<=WMAX){ string c=unpack(SD[0].sl[L],SD[0].len[L],0); W=c+W; pos=c.size()-1; LR[0]=0; continue; }
      Res r=rule(0,L,st);
      if((r.n>=FAIL && r.n!=INPROG) ? (r.n==HALT && !lbok(0,r)) || r.n==STALL : !lbok(0,r)){ r=ruleC(0,L,st,cW[0].data()); if(!(r.n>=FAIL && r.n!=INPROG) || r.n==HALT){ for(int i=0;i<K;i++) r.lb[i]=NEG; r.src[0]=-1; } }
      if(r.n>=FAIL && r.n!=INPROG){ if(r.n==HALT){ applyTop(0,r); why="HALT"; } else why= r.n==NORET?"NORET":"STALL:"+failWhy; break; }
      if(!applyTop(0,r)) break; st=r.q; LR[0]=r.n; pos=0;
    }
  }
  if(getenv("WALLS")) for(int sd=0;sd<2;sd++) for(auto&w:SD[sd].walls) fprintf(stderr,"wallphase side%d %s\n",sd,wkey(w).substr(0,400).c_str());
  double secs=chrono::duration<double>(chrono::steady_clock::now()-t0).count();
  printf("%s %s fix=%d T0=%lld wall=%c steps=%s log10=%.4f top=%lld nodes=%zu/%zu walls=%zu/%zu c=",
    m.c_str(), why.c_str(), FIX, T0, wside, numstr(steps).c_str(), steps>0?log10(numd(steps)):0, top, SD[0].par.size(), SD[1].par.size(), SD[0].walls.size(), SD[1].walls.size());
  int ws = wside=='L'?0:1; for(int i=0;i<K;i++) printf("%.3g%s",numd(cW[ws][i]),i<K-1?",":"");
  printf(" conc=%lld calls=%lld miss=%lld wallMiss=%lld iters=%lld depth=%d secs=%.1f\n", concCalls, ruleCalls, ruleMiss, wallMiss, totalIters, maxDepth, secs);
}
