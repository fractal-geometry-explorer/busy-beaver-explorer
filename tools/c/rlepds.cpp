// rlepds: procedure summaries over an exact side, with a run-length abstraction of the other side.
//
// The tape on one side of the head (the "stack side", left unless `mirror`) is kept exactly, as the stack of a
// pushdown system.  The tape on the other side is abstracted to its K nearest items followed by a tail that is
// either BLANK (0^inf) or ANY (every tape).  An item is a run of one symbol with a count class, or a repetition
// [r1 r2 .. rp]^n of 2..P runs with a count class for n.  A count class is an exact number below E, or
// "at least c and = r mod M" for E <= c <= T (a lower bound that is capped at T).  The copies of a repeated
// pattern are independent: each run of each copy lies in its own class.  The control state of the pushdown system
// is (machine state, cell under the head, abstract other side).
// The forward reachable set is computed with procedure summaries: an entry (control, pushed cell) is the moment
// a cell is pushed, its exits are the controls in which that cell is popped again.  A summary therefore says "from
// this context, whatever lies below on the stack and for every tape in the abstract side, the excursion never
// comes back or comes back in one of these controls": the shape of the certificate nodes of cryptids PR 37.
// Inside one path set a control is not explored when a weaker one (same shape, all lower bounds smaller or equal)
// is already there.  If no reachable control reads a halting transition, the machine never halts.
//
// usage: rlepds MACHINE K P E1 T1 M1 E2 T2 M2 [options]
//   E1,T1,M1: classes of run lengths; E2,T2,M2: classes of repetition counts; P: longest pattern in runs (1 = none)
//   mirror      the stack side is the right side
//   start=N     run the real machine N steps first and analyse from that configuration
//   forget      with start=: replace the abstract side by ANY (the result then holds for every tape on that side)
//   any         from blank tape: tail ANY instead of BLANK
//   slack=S     up to S leading single runs do not count towards K (lets a pattern form before truncation)
//   ctx=D       with start=: keep only the D nearest stack cells and list the ways the excursion leaves them
//   enter=Qh    tail-excursion summary: state Q on cell h, the other side ANY, nothing known on the stack side;
//               lists every way the head can come back to the cell before the starting cell (or NONHALT with no exit)
//   limit=N     give up after N path edges;  selftest=N  check the real run against the reached set (blank start)
//   cert=FILE   write values, entries, path sets and callers
// environment: RLEPDS_SHOW=n prints the last n steps of an abstract path to a halt (tools/py/rlepds_replay.py replays it),
//   RLEPDS_NOSUBS=1 turns subsumption off, RLEPDS_VALS=n samples the abstract values reached.
// prints: RESULT <machine> <params> NONHALT|HALTREACH|LIMIT entries=.. paths=.. vals=..
// Status (26 November 2026): never claims any of the 35 proved halters; proves none of the 64 proved non-halters
// and none of the 509 open holdouts in the settings tried.  See holdouts/recent-proofs/followup/rlepds-nov26.md.
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64; typedef unsigned u32;
// open-addressing set of 64-bit keys (key ~0 is reserved)
struct Set64{ vector<u64> t; size_t n=0, mask=0; Set64(){ t.assign(1<<16,~0ULL); mask=t.size()-1; }
  static inline u64 h(u64 x){ x^=x>>33; x*=0xff51afd7ed558ccdULL; x^=x>>33; x*=0xc4ceb9fe1a85ec53ULL; x^=x>>33; return x; }
  void grow(){ vector<u64> o; o.swap(t); t.assign(o.size()*2,~0ULL); mask=t.size()-1; for(u64 k:o) if(k!=~0ULL){ size_t i=h(k)&mask; while(t[i]!=~0ULL) i=(i+1)&mask; t[i]=k; } }
  bool insert(u64 k){ if(n*2>=t.size()) grow(); size_t i=h(k)&mask; while(t[i]!=~0ULL){ if(t[i]==k) return false; i=(i+1)&mask; } t[i]=k; n++; return true; }
  bool count(u64 k)const{ size_t i=h(k)&mask; while(t[i]!=~0ULL){ if(t[i]==k) return true; i=(i+1)&mask; } return false; }
  size_t size()const{ return n; } };
static int Tw[6][2],Td[6][2],Tn[6][2];
static int K,P,E1,T1,M1,E2,T2,M2,SL=0;
struct Run{ uint8_t sym; uint16_t c; bool operator==(const Run&o)const{return sym==o.sym&&c==o.c;} };
struct Item{ vector<Run> pat; uint16_t rep; };
struct Val{ vector<Item> it; bool blank; };
// count classes: 1..E-1 exact; E+(c-E)*M+r means "n >= c and n = r mod M" for E <= c <= T
static inline uint16_t lb(int c,int r,int E,int M){ return E+(c-E)*M+r; }
static inline uint16_t mk(int n,int E,int T,int M){ return n<E? n : lb(min(n,T),n%M,E,M); }
static inline uint16_t inc(uint16_t x,int E,int T,int M){ if(x<E-1) return x+1; if(x==E-1) return lb(E,E%M,E,M); int c=E+(x-E)/M, r=(x-E)%M; return lb(min(c+1,T),(r+1)%M,E,M); }
// dec: up to two results; 0 means the count reached zero
static inline int dec(uint16_t x,int E,int T,int M,uint16_t out[2]){ (void)T;
  if(x<E){ out[0]=x-1; return 1; }
  int c=E+(x-E)/M, r=(x-E)%M, n=0;
  if(c>E){ out[n++]=lb(c-1,(r-1+M)%M,E,M); return n; }
  out[n++]=lb(E,(r-1+M)%M,E,M); if(E%M==r) out[n++]=E-1; return n; }
static inline bool inClsX(int n,uint16_t x,int E,int M){ if(x<E) return n==x; int c=E+(x-E)/M, r=(x-E)%M; return n>=c && n%M==r; }
static string ser(const Val&v){ string s; s.push_back(v.blank?'B':'A');
  for(auto&i:v.it){ s.push_back((char)i.pat.size()); s.push_back((char)(i.rep&255)); s.push_back((char)(i.rep>>8));
    for(auto&r:i.pat){ s.push_back((char)r.sym); s.push_back((char)(r.c&255)); s.push_back((char)(r.c>>8)); } }
  return s; }
static unordered_map<string,u32> vid; static vector<Val> vals;
static u32 intern(const Val&v){ string s=ser(v); auto it=vid.find(s); if(it!=vid.end()) return it->second; u32 id=vals.size(); vid.emplace(s,id); vals.push_back(v); return id; }
static bool single(const Item&i){ return i.pat.size()==1; }
static Val pushV(int s,Val v){
  if(v.it.empty()&&v.blank&&s==0) return v;
  if(!v.it.empty()&&single(v.it[0])&&v.it[0].pat[0].sym==s) v.it[0].pat[0].c=inc(v.it[0].pat[0].c,E1,T1,M1);
  else { Item i; i.pat.push_back({(uint8_t)s,1}); i.rep=1; v.it.insert(v.it.begin(),i); }
  bool ch=true;
  while(ch){ ch=false;
    for(int p=2;p<=P&&!ch;p++){
      if((int)v.it.size()<p) break;
      bool ok=true; for(int j=0;j<p;j++) if(!single(v.it[j])){ok=false;break;}
      if(!ok) break;
      if((int)v.it.size()>p && (int)v.it[p].pat.size()==p){
        bool eq=true; for(int j=0;j<p;j++) if(!(v.it[j].pat[0]==v.it[p].pat[j])){eq=false;break;}
        if(eq){ v.it.erase(v.it.begin(),v.it.begin()+p); v.it[0].rep=inc(v.it[0].rep,E2,T2,M2); ch=true; break; } }
      if((int)v.it.size()>=2*p){
        bool eq=true; for(int j=0;j<p;j++) if(!single(v.it[p+j])||!(v.it[j].pat[0]==v.it[p+j].pat[0])){eq=false;break;}
        if(eq){ Item n; for(int j=0;j<p;j++) n.pat.push_back(v.it[j].pat[0]); n.rep=mk(2,E2,T2,M2);
          v.it.erase(v.it.begin(),v.it.begin()+2*p); v.it.insert(v.it.begin(),n); ch=true; break; } }
    } }
  int lead=0; while(lead<SL && lead<(int)v.it.size() && single(v.it[lead])) lead++;
  while((int)v.it.size()>K+lead){ v.it.pop_back(); v.blank=false; }
  return v; }
static void popV(const Val&v, vector<pair<int,Val>>&out){
  out.clear();
  if(v.it.empty()){ out.push_back({0,v}); if(!v.blank) out.push_back({1,v}); return; }
  vector<Val> fronts;
  if(single(v.it[0])) fronts.push_back(v);
  else { uint16_t d[2]; int n=dec(v.it[0].rep,E2,T2,M2,d);
    for(int k=0;k<n;k++){ Val w; w.blank=v.blank; const Item&f=v.it[0];
      for(auto&r:f.pat){ Item i; i.pat.push_back(r); i.rep=1; w.it.push_back(i); }
      if(d[k]==1){ for(auto&r:f.pat){ Item i; i.pat.push_back(r); i.rep=1; w.it.push_back(i); } }
      else if(d[k]>1){ Item i=f; i.rep=d[k]; w.it.push_back(i); }
      for(size_t j=1;j<v.it.size();j++) w.it.push_back(v.it[j]);
      fronts.push_back(w); } }
  for(auto&w:fronts){ uint16_t d[2]; int s=w.it[0].pat[0].sym; int n=dec(w.it[0].pat[0].c,E1,T1,M1,d);
    for(int k=0;k<n;k++){ Val x=w; if(d[k]==0) x.it.erase(x.it.begin()); else x.it[0].pat[0].c=d[k];
      if(x.it.size()==1&&x.blank&&single(x.it[0])&&x.it[0].pat[0].sym==0) x.it.clear();
      out.push_back({s,x}); } } }
// does the concrete string (cells nearest first, then 0^inf) lie in gamma(v)?
static bool matchItems(const Val&v,size_t ii,const vector<int>&s,size_t pos);
static bool matchPat(const Val&v,size_t ii,const Item&it,size_t ri,int copies,const vector<int>&s,size_t pos){
  // match runs ri.. of the current copy, `copies` = copies completed so far
  if(ri==it.pat.size()){
    int done=copies+1;
    if(single(it)) return matchItems(v,ii+1,s,pos);
    if(inClsX(done,it.rep,E2,M2) && matchItems(v,ii+1,s,pos)) return true;
    if(done>(int)s.size()+T2+M2+2) return false;
    return matchPat(v,ii,it,0,done,s,pos); }
  const Run&r=it.pat[ri]; size_t lim=s.size()+T1+M1+2;
  for(size_t n=1;n<=lim;n++){
    size_t q=pos+n-1; int cell= q<s.size()? s[q]:0; if(cell!=r.sym) break;
    if(inClsX(n,r.c,E1,M1) && matchPat(v,ii,it,ri+1,copies,s,pos+n)) return true; }
  return false; }
static bool matchItems(const Val&v,size_t ii,const vector<int>&s,size_t pos){
  if(ii==v.it.size()){ if(!v.blank) return true; for(size_t q=pos;q<s.size();q++) if(s[q]) return false; return true; }
  return matchPat(v,ii,v.it[ii],0,0,s,pos); }

static vector<vector<pair<int,u32>>> popCache; static vector<array<int,2>> pushCache;
static void ensure(u32 a){ if(popCache.size()<vals.size()){ popCache.resize(vals.size()); pushCache.resize(vals.size(),array<int,2>{-1,-1}); } (void)a; }
static const vector<pair<int,u32>>& popA(u32 a){ ensure(a); if(popCache[a].empty()){ vector<pair<int,Val>> o; Val v=vals[a]; popV(v,o); vector<pair<int,u32>> r; for(auto&x:o) r.push_back({x.first,intern(x.second)}); ensure(0); popCache[a]=r; } return popCache[a]; }
static u32 pushA(int s,u32 a){ ensure(a); if(pushCache[a][s]<0){ Val v=pushV(s,vals[a]); u32 r=intern(v); ensure(0); pushCache[a][s]=r; } return pushCache[a][s]; }

// shape of a value: every lower bound replaced by the smallest one (residues kept); bounds = the lower bounds, in order
static vector<u32> shapeId; static vector<vector<uint8_t>> boundsOf;
static void shapeOf(u32 a){ if(shapeId.size()<vals.size()){ shapeId.resize(vals.size(),~0u); boundsOf.resize(vals.size()); }
  if(shapeId[a]!=~0u) return; Val v=vals[a]; vector<uint8_t> b;
  for(auto&i:v.it){ for(auto&r:i.pat) if(r.c>=E1){ b.push_back((r.c-E1)/M1); r.c=E1+(r.c-E1)%M1; }
    if(i.rep>=E2 && i.pat.size()>1){ b.push_back((i.rep-E2)/M2); i.rep=E2+(i.rep-E2)%M2; } }
  u32 sidv=intern(v); if(shapeId.size()<vals.size()){ shapeId.resize(vals.size(),~0u); boundsOf.resize(vals.size()); }
  shapeId[a]=sidv; boundsOf[a]=b; }
static string showVal(const Val&v){ string s; auto cl=[&](uint16_t x,int E,int M){ if(x<E) return to_string(x); return string(">=")+to_string(E+(x-E)/M)+"%"+to_string(M)+"="+to_string((x-E)%M); };
  for(auto&i:v.it){ if(single(i)){ s+=to_string(i.pat[0].sym)+"^"+cl(i.pat[0].c,E1,M1)+" "; }
    else { s+="["; for(auto&r:i.pat) s+=to_string(r.sym)+"^"+cl(r.c,E1,M1)+" "; s+="]^"+cl(i.rep,E2,M2)+" "; } }
  s+= v.blank?"BLANK":"ANY"; return s; }

int main(int argc,char**argv){
  if(argc<10){ fprintf(stderr,"usage: rlepds MACHINE K P E1 T1 M1 E2 T2 M2 [mirror] [limit=N] [selftest=N] [cert=FILE] [any] [start=N] [forget] [slack=S]\n"); return 2; }
  string m=argv[1]; K=atoi(argv[2]); P=atoi(argv[3]); E1=atoi(argv[4]); T1=atoi(argv[5]); M1=atoi(argv[6]); E2=atoi(argv[7]); T2=atoi(argv[8]); M2=atoi(argv[9]);
  if(E1<2||E2<3||M1<1||M2<1||T1<E1||T2<E2){ fprintf(stderr,"need E1>=2, E2>=3, T>=E\n"); return 2; }
  bool mir=false, anyTail=false; u64 limit=50000000; long selftest=0, startN=0; bool forget=false; int ctxD=-1, enterQ=-1, enterH=0; string certf;
  for(int i=10;i<argc;i++){ string a=argv[i]; if(a=="mirror") mir=true; else if(a=="any") anyTail=true; else if(a.rfind("limit=",0)==0) limit=atoll(a.c_str()+6); else if(a.rfind("selftest=",0)==0) selftest=atol(a.c_str()+9); else if(a.rfind("cert=",0)==0) certf=a.substr(5); else if(a.rfind("start=",0)==0) startN=atol(a.c_str()+6); else if(a=="forget") forget=true; else if(a.rfind("slack=",0)==0) SL=atoi(a.c_str()+6); else if(a.rfind("ctx=",0)==0) ctxD=atoi(a.c_str()+4); else if(a.rfind("enter=",0)==0){ enterQ=a[6]-'A'; enterH=a[7]-'0'; ctxD=0; anyTail=true; } }
  int ns=(m.size()+1)/7;
  for(int s=0;s<6;s++)for(int b=0;b<2;b++) Tn[s][b]=-1;
  for(int s=0;s<ns;s++)for(int b=0;b<2;b++){ string x=m.substr(7*s+3*b,3); if(x[0]=='-'||x[2]=='-'){Tn[s][b]=-1;continue;} Tw[s][b]=x[0]-'0'; Td[s][b]=(x[1]=='R')?1:-1; if(mir) Td[s][b]=-Td[s][b]; Tn[s][b]=x[2]-'A'; }
  // stack side = "left" (after mirroring).  dir +1 = away from the stack (push), -1 = towards it (pop)
  Val v0; v0.blank=!anyTail; u32 a0=intern(v0);
  auto ctl=[&](int q,int h,u32 a)->u32{ return a*12+q*2+h; };
  // entries: 0 = root; else (control, pushed symbol)
  unordered_map<u64,u32> eid; vector<u64> ekey; ekey.push_back(~0ULL);
  vector<vector<u32>> exits(1), callers(1), paths(1);
  Set64 pathSet, exitSet, callSet; bool keepPaths=false;
  vector<pair<u32,u32>> work; Set64 ctxExitSet; vector<u32> ctxExits;
  bool halted=false, over=false; u32 haltE=0, haltC=0;
  bool trace=getenv("RLEPDS_SHOW")!=0; u64 cur=~0ULL; u32 viaE=0;
  // witness: for a path (e,c): pk = predecessor config key in the same entry (or ~0 at the entry's start), pv = callee entry if
  // the step is a call+return (then the callee's exit is c), 0 for a plain step.  exitBy[(e2,x)] = config of e2 that pops to x.
  // entryBy[e2] = (caller entry, caller config) that first pushed it.
  unordered_map<u64,u32> callSiteFirst; unordered_map<u64,pair<u64,u32>> par; unordered_map<u64,u64> exitBy; unordered_map<u32,u64> entryBy;
  // subsumption inside one path set: a control is not explored when a weaker one (same shape, lower bounds all <=) is there
  bool subs=!getenv("RLEPDS_NOSUBS"); unordered_map<u64,vector<u32>> minimal; size_t skipped=0;
  auto weaker=[&](u32 y,u32 x){ auto&by=boundsOf[y]; auto&bx=boundsOf[x]; for(size_t i=0;i<bx.size();i++) if(by[i]>bx[i]) return false; return true; };
  auto addPath=[&](u32 e,u32 c){
    if(pathSet.count(((u64)e<<32)|c)) return;
    if(subs){ u32 a=c/12; shapeOf(a);
      if(!boundsOf[a].empty()){ auto&L=minimal[((u64)e<<32)|((u64)shapeId[a]*12+c%12)];
        for(u32 y:L) if(weaker(y,a)){ skipped++; return; }
        size_t k=0; for(size_t i=0;i<L.size();i++) if(!weaker(a,L[i])) L[k++]=L[i]; L.resize(k); L.push_back(a); } }
    pathSet.insert(((u64)e<<32)|c); if(keepPaths) paths[e].push_back(c); work.push_back({e,c}); if(trace) par[((u64)e<<32)|c]={cur,viaE}; };
  auto getEntry=[&](u32 c,int w)->u32{ u64 k=(u64)c*2+w; auto it=eid.find(k); if(it!=eid.end()) return it->second; u32 id=ekey.size(); eid.emplace(k,id); ekey.push_back(k); exits.emplace_back(); callers.emplace_back(); paths.emplace_back(); return id; };
  keepPaths=!certf.empty()||getenv("RLEPDS_SUBS")||selftest>0;
  int q0=0,h0=0; u32 e0=0; vector<int> st0, ot0;
  if(startN>0){ // run the real machine startN steps, then start the analysis from that configuration
    for(long t=0;t<startN;t++){ if(Tn[q0][h0]<0){ printf("RESULT %s halts at step %ld\n",m.c_str(),t); return 1; }
      int w=Tw[q0][h0], d=Td[q0][h0]; q0=Tn[q0][h0];
      if(d>0){ st0.push_back(w); if(ot0.empty()) h0=0; else { h0=ot0.back(); ot0.pop_back(); } }
      else { ot0.push_back(w); if(st0.empty()) h0=0; else { h0=st0.back(); st0.pop_back(); } } }
    Val v=v0; if(forget) v.blank=false; else for(int x:ot0) v=pushV(x,v);
    a0=intern(v);
    size_t z=0; while(z<st0.size()&&st0[z]==0) z++;
    if(ctxD>=0){ z= st0.size()>(size_t)ctxD? st0.size()-ctxD : 0; }
    for(size_t i=z;i<st0.size();i++){ u32 id=ekey.size(); ekey.push_back((1ULL<<62)+st0[i]); exits.emplace_back(); callers.emplace_back(); paths.emplace_back(); callers[id].push_back(e0); callSet.insert(((u64)id<<32)|e0); e0=id; } }
  if(enterQ>=0){ q0=enterQ; h0=enterH; }
  addPath(e0,ctl(q0,h0,a0));
  while(!work.empty()){
    auto [e,c]=work.back(); work.pop_back(); cur=((u64)e<<32)|c;
    if(pathSet.size()>limit){ over=true; break; }
    int q=(c%12)/2, h=c%2; u32 a=c/12;
    if(subs && !boundsOf[a].empty()){ auto&L=minimal[((u64)e<<32)|((u64)shapeId[a]*12+c%12)]; bool in=false; for(u32 y:L) if(y==a){in=true;break;} if(!in){ skipped++; continue; } }
    if(Tn[q][h]<0){ halted=true; haltE=e; haltC=c; break; }
    int w=Tw[q][h], d=Td[q][h], q2=Tn[q][h];
    if(d>0){ // move away from the stack: push w, read next cell from the abstract side
      vector<pair<int,u32>> pp=popA(a);
      for(auto&[h2,a2]:pp){ u32 c2=ctl(q2,h2,a2); u32 e2=getEntry(c2,w);
        if(trace && !entryBy.count(e2)) entryBy[e2]=cur;
        if(callSet.insert(((u64)e2<<32)|e)){ callers[e2].push_back(e); callSiteFirst[((u64)e2<<32)|e]=c; viaE=e2; for(size_t i=0;i<exits[e2].size();i++) addPath(e,exits[e2][i]); viaE=0; }
        { u64 sv=cur; cur=~0ULL; addPath(e2,c2); cur=sv; } }
    } else { u32 a2=pushA(w,a);
      if(e==0){ if(ctxD>=0){ if(ctxExitSet.insert(ctl(q2,0,a2))) ctxExits.push_back(ctl(q2,0,a2)); } else addPath(0,ctl(q2,0,a2)); }
      else { int we=ekey[e]&1; u32 x=ctl(q2,we,a2);
        if(exitSet.insert(((u64)e<<32)|x)){ exits[e].push_back(x); if(trace) exitBy[((u64)e<<32)|x]=cur;
          // each caller config that pushed into e continues at x; the predecessor inside the caller is not known here,
          // so the witness for (caller,x) is rebuilt from entryBy / callSite below
          for(size_t i=0;i<callers[e].size();i++){ u64 sv=cur; u32 ce=callers[e][i]; { auto f=callSiteFirst.find(((u64)e<<32)|ce); cur= f==callSiteFirst.end()? ~0ULL : (((u64)ce<<32)|f->second); } viaE=e; addPath(ce,x); viaE=0; cur=sv; } } } }
  }
  const char*res= halted?"HALTREACH": over?"LIMIT":"NONHALT";
  printf("RESULT %s K=%d P=%d E1=%d T1=%d M1=%d E2=%d T2=%d M2=%d SL=%d %s%s %s entries=%zu paths=%zu vals=%zu\n",m.c_str(),K,P,E1,T1,M1,E2,T2,M2,SL,mir?"mirror":"plain",anyTail?" any":"",res,ekey.size(),pathSet.size(),vals.size());
  if(halted && trace){
    vector<u32> out; // controls in temporal order
    // iterative expansion with an explicit stack of tasks: (kind, e, c): kind 0 = emit witness from the start of e to (e,c) inclusive
    function<void(u32,u32)> wit=[&](u32 e,u32 c){
      vector<pair<u32,u32>> chain; // configs of e from c back to the start
      u64 k=((u64)e<<32)|c;
      vector<pair<u64,u32>> back;
      while(true){ auto pr=par[k]; back.push_back({k,pr.second}); u64 pk=pr.first;
        if(pk==~0ULL) break;
        k=pk; }
      for(size_t i=back.size();i-->0;){ u32 cc=(u32)back[i].first; u32 via=back[i].second;
        if(via){ // the callee excursion happened before reaching cc: emit it
          u64 prod=exitBy[((u64)via<<32)|cc]; wit(via,(u32)prod); }
        out.push_back(cc); } };
    // chain of entries from the root (or the start chain) down to haltE
    vector<pair<u32,u32>> stk; { u32 e=haltE; u32 c=haltC; while(true){ stk.push_back({e,c}); auto it=entryBy.find(e); if(it==entryBy.end()) break; u64 k=it->second; e=k>>32; c=(u32)k; } }
    for(size_t i=stk.size();i-->0;) wit(stk[i].first,stk[i].second);
    size_t lim=atol(getenv("RLEPDS_SHOW")); size_t st= out.size()>lim? out.size()-lim:0;
    for(size_t i=st;i<out.size();i++){ u32 c=out[i]; printf("  %c reads %d | %s\n",'A'+(c%12)/2,c%2,showVal(vals[c/12]).c_str()); } }
  if(ctxD>=0 && !halted && !over){ printf("context summary: the %d cells kept on the stack side are left in %zu ways (state after the pop, abstract side); the cell read next is below the context\n",ctxD,ctxExits.size());
    for(u32 x:ctxExits) printf("  exit %c | %s\n",'A'+(x%12)/2,showVal(vals[x/12]).c_str()); }
  if(getenv("RLEPDS_SUBS")){ // how many reached controls are dominated by a weaker control in the same path set?
    size_t dom=0,tot=0;
    for(size_t e=0;e<paths.size();e++){ map<u64,vector<u32>> g; for(u32 c:paths[e]){ shapeOf(c/12); g[(u64)shapeId[c/12]*12+c%12].push_back(c/12); }
      for(auto&kv:g){ auto&L=kv.second; tot+=L.size(); if(L.size()<2) continue;
        for(u32 a:L){ bool d=false; for(u32 b:L){ if(a==b) continue; auto&x=boundsOf[a]; auto&y=boundsOf[b]; bool le=true; for(size_t i=0;i<x.size();i++) if(y[i]>x[i]){le=false;break;} if(le){d=true;break;} } dom+=d; } } }
    printf("SUBS dominated %zu of %zu path edges\n",dom,tot); }
  if(getenv("RLEPDS_VALS")){ size_t n=atoi(getenv("RLEPDS_VALS")); for(size_t i=0;i<n;i++){ size_t j=(u64)i*vals.size()/n; printf("  val %zu: %s\n",j,showVal(vals[j]).c_str()); } }
  if(selftest>0 && !halted && !over){
    // follow the real run; at every step some element of the path set of a possible top entry must contain the real
    // configuration (gamma membership of the abstract side, exact stack by the chain of entries)
    if(startN>0){ printf("selftest not supported with start=\n"); return 0; }
    vector<int> st, ot; int q=0,h=0; vector<set<u32>> ent; ent.push_back({0}); long bad=0;
    for(long t=0;t<selftest;t++){
      vector<int> s(ot.rbegin(),ot.rend());
      vector<pair<u32,u32>> good;
      for(u32 e:ent.back()) for(u32 c:paths[e]) if((int)(c%12)==q*2+h && matchItems(vals[c/12],0,s,0)) good.push_back({e,c});
      if(good.empty()){ printf("SELFTEST FAIL step %ld: real configuration not in the reached set\n",t); bad++; break; }
      if(Tn[q][h]<0){ printf("SELFTEST: real run halts at %ld\n",t); break; }
      int w=Tw[q][h], d=Td[q][h], q2=Tn[q][h];
      if(d>0){ int h2= ot.empty()?0:ot.back(); if(!ot.empty()) ot.pop_back(); set<u32> ne;
        for(auto&[e,c]:good) for(auto&[hh,a2]:popA(c/12)) if(hh==h2){ auto it=eid.find((u64)ctl(q2,h2,a2)*2+w); if(it!=eid.end() && callSet.count(((u64)it->second<<32)|e)) ne.insert(it->second); }
        st.push_back(w); ent.push_back(ne); h=h2; q=q2;
      } else { ot.push_back(w); if(st.empty()){ h=0; } else { h=st.back(); st.pop_back(); ent.pop_back(); } q=q2; }
    }
    if(!bad) printf("SELFTEST OK %ld steps\n",selftest);
  }
  if(!certf.empty() && !halted && !over){
    FILE*f=fopen(certf.c_str(),"w");
    fprintf(f,"rlepds-cert 2\nmachine %s\nparams %d %d %d %d %d %d %d %d %d %d %d %ld %d\n",m.c_str(),K,P,E1,T1,M1,E2,T2,M2,SL,mir?1:0,anyTail?1:0,startN,forget?1:0);
    fprintf(f,"vals %zu\n",vals.size());
    for(auto&v:vals){ fprintf(f,"%c %zu",v.blank?'B':'A',v.it.size()); for(auto&i:v.it){ fprintf(f," %zu %d",i.pat.size(),i.rep); for(auto&r:i.pat) fprintf(f," %d %d",r.sym,r.c); } fprintf(f,"\n"); }
    fprintf(f,"entries %zu\n",ekey.size());
    for(size_t e=0;e<ekey.size();e++){ if(e==0) fprintf(f,"root"); else fprintf(f,"%llu %d",(unsigned long long)(ekey[e]/2),(int)(ekey[e]&1));
      fprintf(f," | %zu",paths[e].size()); for(u32 c:paths[e]) fprintf(f," %u",c);
      fprintf(f," | %zu",callers[e].size()); for(u32 c:callers[e]) fprintf(f," %u",c); fprintf(f,"\n"); }
    fclose(f); }
  return halted?1: over?3:0; }
