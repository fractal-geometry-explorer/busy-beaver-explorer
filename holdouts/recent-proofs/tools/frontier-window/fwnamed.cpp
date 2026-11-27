// fwnamed: the frontier-window decider (fwdec.cpp) with call-named classes.
//
// As in fwdec, the tape is an exact window of TW cells at the left frontier plus a half tape known by a class,
// and a step from the window into the half tape is a call with a summary. Here a class is a pair
//   (first K cells, name),
// where the name says which call left the half tape behind: (entry state, first K cells of the called class,
// return state), followed by the name of the called class, cut to DEPTH levels (the idea of tokgram.cpp, on
// cells instead of run tokens). DEPTH = 0 gives fwdec. A class is unfolded into the (cell, class) pairs that
// were put into it, so the classes are the nonterminals of a right-linear grammar. Any naming is sound: the
// language of a class is defined by the pairs put into it.
// The start is the real configuration at the first step >= T0 where the head is inside the window; the rest of
// the tape at that moment is given exactly, one class per cell.
//
// Usage: [T0=steps] fwnamed MACHINE L|R TW K DEPTH [MAXTOP=30000000] [CERT=file]
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64; typedef unsigned u32;
static int W[6][2],D[6][2],NX[6][2];
static int TW,K,DEPTH; static u64 WMASK; static long MAXTOP=30000000, MAXCLS=3000000;
static inline u32 phi(int c,u32 p){ int len=31-__builtin_clz(p); u32 bits=p^(1u<<len); bits=(bits<<1)|c; len++; if(len>K){ len=K; bits&=(1u<<K)-1; } return (1u<<len)|bits; }
// names
static vector<vector<u64>> names; static map<vector<u64>,u32> namemap;
static u32 nameid(const vector<u64>&v){ auto it=namemap.find(v); if(it!=namemap.end()) return it->second; u32 id=names.size(); names.push_back(v); namemap[v]=id; return id; }
// classes: 0 = blank
static vector<u32> cpre, cname; static unordered_map<u64,u32> clsmap;
static vector<vector<pair<int,u32>>> U; static vector<vector<u32>> udeps;
static vector<vector<u32>> Sum, deps; static vector<char> known, inwork; struct TN { u64 win; u32 q; unsigned char a,i; };
static vector<vector<TN>> topwait;
static u32 clsid(u32 pre,u32 nm){ u64 k=((u64)nm<<32)|pre; auto it=clsmap.find(k); if(it!=clsmap.end()) return it->second; u32 id=cpre.size(); cpre.push_back(pre); cname.push_back(nm); clsmap[k]=id;
  U.emplace_back(); udeps.emplace_back(); for(int j=0;j<6;j++){ Sum.emplace_back(); deps.emplace_back(); known.push_back(0); inwork.push_back(0); topwait.emplace_back(); } return id; }
static deque<long> work; static long nfacts=0, ntrans=0, ncontracts=0;
static vector<pair<u32,u32>> newfacts; static vector<u32> factS; // facts stored as index into pairs
static void push(long c){ if(c<0){ work.push_back(c); return; } if(!inwork[c]){ inwork[c]=1; work.push_back(c); } }
static void need(u32 c){ if(!known[c]){ known[c]=1; ncontracts++; push(c); } }
static u32 mk(int c,u32 qi,u32 nm){ u32 r; if(qi==0&&c==0) r=0; else r=clsid(phi(c,cpre[qi]),nm);
  auto &u=U[r]; pair<int,u32> x(c,qi); if(find(u.begin(),u.end(),x)==u.end()){ u.push_back(x); ntrans++; for(u32 d:udeps[r]) push(d); } return r; }
static u32 callname(int s,u32 q,int a2){ if(DEPTH==0) return 1; vector<u64> v; v.push_back(((u64)cpre[q]<<6)|(a2<<3)|s); const auto&p=names[cname[q]]; for(size_t j=0;j<p.size()&&(int)v.size()<DEPTH;j++) v.push_back(p[j]); return nameid(v); }
static bool halted=false; static string haltinfo;
// a fact is (s2, q2) packed in u64 inside vector<u32> pairs: Sum[id] holds indices into factA/factB
static vector<u32> fq; static vector<unsigned char> fs;
static bool addfact(u32 id,int s2,u32 q2){ auto&v=Sum[id]; for(u32 f:v) if(fq[f]==q2&&fs[f]==s2) return false; u32 f=fq.size(); fq.push_back(q2); fs.push_back(s2); v.push_back(f); nfacts++; newfacts.push_back({id,f}); return true; }
static void evalc(u32 id){ int s=id%6; u32 q=id/6; { auto&ud=udeps[q]; if(find(ud.begin(),ud.end(),id)==ud.end()) ud.push_back(id); }
  vector<u64> st; unordered_set<u64> seen; auto add=[&](int a,int c,u32 qi){ u64 m=((u64)qi<<4)|(a<<1)|c; if(seen.insert(m).second) st.push_back(m); };
  { auto u=U[q]; for(auto&x:u) add(s,x.first,x.second); }
  bool changed=false;
  while(!st.empty()){ u64 m=st.back(); st.pop_back(); int c1=m&1, a=(m>>1)&7; u32 qi=m>>4;
    if(NX[a][c1]<0){ halted=true; haltinfo="inside a call"; return; }
    int w=W[a][c1], d=D[a][c1], a2=NX[a][c1];
    if(d<0){ u32 r=mk(w,qi,callname(s,q,a2)); if(addfact(id,a2,r)) changed=true; }
    else { u32 cc=qi*6+a2; need(cc); auto&dp=deps[cc]; if(find(dp.begin(),dp.end(),id)==dp.end()) dp.push_back(id);
      auto tmp=Sum[cc]; for(u32 f:tmp) add(fs[f],w,fq[f]); } }
  if(changed){ auto dp=deps[id]; for(u32 d_:dp) push(d_); } }
struct Tab { vector<TN> t; vector<char> used; size_t n=0, mask=0;
  void init(size_t cap){ t.assign(cap,TN{0,0,0,0}); used.assign(cap,0); mask=cap-1; n=0; }
  static size_t h(const TN&x){ u64 v=x.win*0x9E3779B97F4A7C15ULL ^ ((u64)x.q<<16 | (u64)x.a<<8 | x.i)*0xC2B2AE3D27D4EB4FULL; v^=v>>29; v*=0xBF58476D1CE4E5B9ULL; v^=v>>32; return v; }
  bool ins(const TN&x){ if(n*2>mask) grow(); size_t k=h(x)&mask; while(used[k]){ if(t[k].win==x.win&&t[k].q==x.q&&t[k].a==x.a&&t[k].i==x.i) return false; k=(k+1)&mask; } used[k]=1; t[k]=x; n++; return true; }
  void grow(){ vector<TN> o; o.swap(t); vector<char> ou; ou.swap(used); init((mask+1)*2); for(size_t k=0;k<o.size();k++) if(ou[k]) ins(o[k]); } };
static Tab tab; static vector<TN> topst;
static void addtop(int a,int i,u64 win,u32 q){ TN x{win,q,(unsigned char)a,(unsigned char)i}; if(tab.ins(x)) topst.push_back(x); }
static void evaltop(){
  while(!topst.empty()){ if((long)tab.n>MAXTOP) return; TN n=topst.back(); topst.pop_back(); int a=n.a, c=(n.win>>n.i)&1;
    if(NX[a][c]<0){ halted=true; haltinfo="at the frontier"; return; }
    int w=W[a][c], d=D[a][c], a2=NX[a][c]; u64 win=(n.win&~(1ULL<<n.i))|((u64)w<<n.i);
    if(d<0){ if(n.i>0) addtop(a2,n.i-1,win,n.q); else { u32 q2=mk((win>>(TW-1))&1,n.q, n.q==0? 1u : cname[n.q]); addtop(a2,0,(win<<1)&WMASK,q2); } }
    else if(n.i<TW-1) addtop(a2,n.i+1,win,n.q);
    else { u32 cc=n.q*6+a2; need(cc); TN nw{win,n.q,(unsigned char)a2,n.i}; topwait[cc].push_back(nw);
      auto tmp=Sum[cc]; for(u32 f:tmp) addtop(fs[f],TW-1,win,fq[f]); } } }
int main(int argc,char**argv){
  if(argc<6){ fprintf(stderr,"usage: [T0=steps] fwnamed MACHINE L|R TW K DEPTH [MAXTOP] [CERT]\n"); return 2; }
  char*m=argv[1]; bool mirror=argv[2][0]=='R'; TW=atoi(argv[3]); K=atoi(argv[4]); DEPTH=atoi(argv[5]); if(argc>6) MAXTOP=atol(argv[6]); const char*dump= argc>7? argv[7]:0;
  if(getenv("MAXCLS")) MAXCLS=atol(getenv("MAXCLS"));
  if(TW<1||TW>64||K<0||K>24){ fprintf(stderr,"need 1<=TW<=64, 0<=K<=24\n"); return 2; }
  WMASK= TW==64? ~0ULL : ((1ULL<<TW)-1);
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*x=m+7*s+3*b; if(x[0]=='-'){NX[s][b]=-1;continue;} W[s][b]=x[0]-'0'; D[s][b]=x[1]=='R'?1:-1; if(mirror)D[s][b]=-D[s][b]; NX[s][b]=x[2]-'A';}
  nameid(vector<u64>{~0ULL}); nameid(vector<u64>{});            // 0 = blank, 1 = no name
  clsid(1,0); U[0].push_back({0,0}); ntrans=1; tab.init(1<<16);
  // seed: the real configuration at the first step >= T0 with the head inside the window
  long T0= getenv("T0")? atol(getenv("T0")):0; long t=0; int s0=0; long pos0=0; u64 win0=0; u32 q0=0;
  { long S=1L<<26; vector<unsigned char> tape(S,0); long p=S/2, lo=p, hi=p; int s=0;
    for(;;t++){ if(t>=T0 && p<lo+TW) break; int b=tape[p]; if(NX[s][b]<0){ printf("%s %c : HALTS in the seed run at step %ld\n",m,argv[2][0],t); return 1; }
      tape[p]=W[s][b]; int d=D[s][b]; s=NX[s][b]; p+=d; if(p<lo)lo=p; if(p>hi)hi=p; if(t>T0+300000000L){ printf("%s %c : NOSEED\n",m,argv[2][0]); return 3; } }
    s0=s; pos0=p-lo; for(int j=0;j<TW;j++) win0|=(u64)tape[lo+j]<<j;
    long e=hi; while(e>=lo+TW && tape[e]==0) e--;
    u32 q=0; for(long x=e;x>=lo+TW;x--){ u32 nm=nameid(vector<u64>{(1ULL<<62)|(u64)(x-lo)}); q=mk(tape[x],q,nm); } q0=q; }
  auto t0=chrono::steady_clock::now(); addtop(s0,pos0,win0,q0); TN seed{win0,q0,(unsigned char)s0,(unsigned char)pos0}; push(-1); bool limit=false;
  while(!work.empty()){ long c=work.front(); work.pop_front();
    if(c==-1) evaltop(); else { inwork[c]=0; evalc(c); }
    if(halted) break;
    if(!newfacts.empty()){ vector<pair<u32,u32>> nf; nf.swap(newfacts); for(auto&f:nf){ auto ws=topwait[f.first]; for(auto&n:ws) addtop(fs[f.second],TW-1,n.win,fq[f.second]); } }
    if((long)tab.n>MAXTOP || (long)cpre.size()>MAXCLS){ limit=true; break; }
    if(!topst.empty()) push(-1); }
  printf("%s %c TW=%d K=%d D=%d T0=%ld : %s classes=%zu names=%zu trans=%ld contracts=%ld facts=%ld top=%zu %.1fs %s\n",m,argv[2][0],TW,K,DEPTH,t, halted?"HALT-REACHABLE":(limit?"LIMIT":"NONHALT"),cpre.size(),names.size(),ntrans,ncontracts,nfacts,tab.n,chrono::duration<double>(chrono::steady_clock::now()-t0).count(),haltinfo.c_str());
  if(dump && !halted && !limit){ FILE*f=fopen(dump,"w"); fprintf(f,"machine %s %c\nwindow %d prefix %d depth %d\n",m,argv[2][0],TW,K,DEPTH);
    string w(TW,'0'); for(int j=0;j<TW;j++) w[j]='0'+((seed.win>>j)&1); fprintf(f,"S %ld %d %d %s %u\n",t,seed.a,seed.i,w.c_str(),seed.q);
    for(size_t r=0;r<U.size();r++) for(auto&x:U[r]) fprintf(f,"T %d %u %zu\n",x.first,x.second,r);
    for(size_t c=0;c<Sum.size();c++) for(u32 x:Sum[c]) fprintf(f,"F %d %zu %d %u\n",(int)(c%6),c/6,(int)fs[x],fq[x]);
    for(size_t k=0;k<tab.t.size();k++) if(tab.used[k]){ auto&x=tab.t[k]; for(int j=0;j<TW;j++) w[j]='0'+((x.win>>j)&1); fprintf(f,"P %d %d %s %u\n",x.a,x.i,w.c_str(),x.q); }
    fclose(f); }
  return halted?1:(limit?3:0); }
