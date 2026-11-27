// fwdec: frontier-window decider. A sound non-halting decider for Turing machines with 2 symbols.
//
// The tape is cut into two parts. (1) An exact window of TW cells that starts at the left frontier (the
// leftmost cell the head has reached); everything left of it is blank. (2) The rest, a half tape, known only
// by a class: its first K cells (or all of it, if it has fewer than K cells before the blank).
// A step of the head from the last window cell into the half tape is a CALL. A call (entry state, class) has a
// summary: the set of (return state, class afterwards). The summary of a class is computed by unfolding the
// class into one cell and a class one cell further right, running that cell, and answering the calls it makes
// from the summaries one level down. Summaries, the unfoldings in use and the set of top-level configurations
// grow together to a least fixed point. If no halting transition is reachable, the machine never halts
// (induction on the number of steps: a call that returns is made of shorter calls).
//
// Usage: fwdec MACHINE L|R TW K [MAXTOP=30000000] [CERT=file]
//   L: frontier at the left end. R: mirror image. Prints one line; NONHALT means proved (check with check_cert.py).
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64; typedef unsigned u32;
static int W[6][2],D[6][2],NX[6][2];
static int TW,K; static u64 WMASK;
// classes: id = (1<<len) | bits, len <= K, bit j = cell j. id 1 = blank.
static inline u32 phi(int c,u32 q){ if(q==1&&c==0) return 1; int len=31-__builtin_clz(q); u32 bits=q^(1u<<len); bits=(bits<<1)|c; len++; if(len>K){ len=K; bits&=(1u<<K)-1; } return (1u<<len)|bits; }
static vector<vector<pair<int,u32>>> U; static vector<vector<u32>> udeps;  // per class
static vector<vector<u32>> Sum, deps; static vector<char> known, inwork;   // per contract q*6+s; fact = s2 | q2<<3
static deque<long> work; static long nfacts=0, ntrans=0, ncontracts=0;
static vector<pair<u32,u32>> newfacts;
static void push(long c){ if(c<0){ work.push_back(c); return; } if(!inwork[c]){ inwork[c]=1; work.push_back(c); } }
static void need(u32 c){ if(!known[c]){ known[c]=1; ncontracts++; push(c); } }
static u32 mk(int c,u32 qi){ u32 r=phi(c,qi); auto &u=U[r]; pair<int,u32> x(c,qi); if(find(u.begin(),u.end(),x)==u.end()){ u.push_back(x); ntrans++; for(u32 d:udeps[r]) push(d); } return r; }
static bool halted=false; static string haltinfo;
static bool addfact(u32 id,u32 f){ auto&v=Sum[id]; if(find(v.begin(),v.end(),f)!=v.end()) return false; v.push_back(f); nfacts++; newfacts.push_back({id,f}); return true; }
static void evalc(u32 id){ int s=id%6; u32 q=id/6; { auto&ud=udeps[q]; if(find(ud.begin(),ud.end(),id)==ud.end()) ud.push_back(id); }
  vector<u64> st; unordered_set<u64> seen; auto add=[&](int a,int c,u32 qi){ u64 m=((u64)qi<<4)|(a<<1)|c; if(seen.insert(m).second) st.push_back(m); };
  { auto u=U[q]; for(auto&x:u) add(s,x.first,x.second); }
  bool changed=false;
  while(!st.empty()){ u64 m=st.back(); st.pop_back(); int c1=m&1, a=(m>>1)&7; u32 qi=m>>4;
    if(NX[a][c1]<0){ halted=true; haltinfo="inside a call"; return; }
    int w=W[a][c1], d=D[a][c1], a2=NX[a][c1];
    if(d<0){ u32 r=mk(w,qi); if(addfact(id,a2|(r<<3))) changed=true; }
    else { u32 cc=qi*6+a2; need(cc); auto&dp=deps[cc]; if(find(dp.begin(),dp.end(),id)==dp.end()) dp.push_back(id);
      auto tmp=Sum[cc]; for(u32 f:tmp) add(f&7,w,f>>3); } }
  if(changed){ auto dp=deps[id]; for(u32 d_:dp) push(d_); } }
// top level
struct TN { u64 win; u32 q; unsigned char a,i; };
struct Tab { vector<TN> t; vector<char> used; size_t n=0, mask=0;
  void init(size_t cap){ t.assign(cap,TN{0,0,0,0}); used.assign(cap,0); mask=cap-1; n=0; }
  static size_t h(const TN&x){ u64 v=x.win*0x9E3779B97F4A7C15ULL ^ ((u64)x.q<<16 | (u64)x.a<<8 | x.i)*0xC2B2AE3D27D4EB4FULL; v^=v>>29; v*=0xBF58476D1CE4E5B9ULL; v^=v>>32; return v; }
  bool ins(const TN&x){ if(n*2>mask) grow(); size_t k=h(x)&mask; while(used[k]){ if(t[k].win==x.win&&t[k].q==x.q&&t[k].a==x.a&&t[k].i==x.i) return false; k=(k+1)&mask; } used[k]=1; t[k]=x; n++; return true; }
  void grow(){ vector<TN> o; o.swap(t); vector<char> ou; ou.swap(used); init((mask+1)*2); for(size_t k=0;k<o.size();k++) if(ou[k]) ins(o[k]); } };
static long MAXTOP=30000000; static Tab tab; static vector<TN> topst; static vector<vector<TN>> topwait;
static void addtop(int a,int i,u64 win,u32 q){ TN x{win,q,(unsigned char)a,(unsigned char)i}; if(tab.ins(x)) topst.push_back(x); }
static void evaltop(){
  while(!topst.empty()){ if((long)tab.n>MAXTOP) return; TN n=topst.back(); topst.pop_back(); int a=n.a, c=(n.win>>n.i)&1;
    if(NX[a][c]<0){ halted=true; haltinfo="at the frontier"; return; }
    int w=W[a][c], d=D[a][c], a2=NX[a][c]; u64 win=(n.win&~(1ULL<<n.i))|((u64)w<<n.i);
    if(d<0){ if(n.i>0) addtop(a2,n.i-1,win,n.q); else { u32 q2=mk((win>>(TW-1))&1,n.q); addtop(a2,0,(win<<1)&WMASK,q2); } }
    else if(n.i<TW-1) addtop(a2,n.i+1,win,n.q);
    else { u32 cc=n.q*6+a2; need(cc); TN nw{win,n.q,(unsigned char)a2,n.i}; topwait[cc].push_back(nw);
      auto tmp=Sum[cc]; for(u32 f:tmp) addtop(f&7,TW-1,win,f>>3); } } }
int main(int argc,char**argv){
  if(argc<5){ fprintf(stderr,"usage: fwdec MACHINE L|R TW K [MAXTOP] [CERT]\n"); return 2; }
  char*m=argv[1]; bool mirror=argv[2][0]=='R'; TW=atoi(argv[3]); K=atoi(argv[4]); if(argc>5) MAXTOP=atol(argv[5]); const char*dump= argc>6? argv[6]:0;
  if(TW<1||TW>64||K<0||K>24){ fprintf(stderr,"need 1<=TW<=64, 0<=K<=24\n"); return 2; }
  WMASK= TW==64? ~0ULL : ((1ULL<<TW)-1);
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*x=m+7*s+3*b; if(x[0]=='-'){NX[s][b]=-1;continue;} W[s][b]=x[0]-'0'; D[s][b]=x[1]=='R'?1:-1; if(mirror)D[s][b]=-D[s][b]; NX[s][b]=x[2]-'A';}
  size_t NQ=(size_t)2<<K; U.resize(NQ); udeps.resize(NQ); Sum.resize(NQ*6); deps.resize(NQ*6); known.assign(NQ*6,0); inwork.assign(NQ*6,0); topwait.resize(NQ*6);
  U[1].push_back({0,1}); ntrans=1; tab.init(1<<16);
  auto t0=chrono::steady_clock::now(); addtop(0,0,0,1); push(-1); bool limit=false;
  while(!work.empty()){ long c=work.front(); work.pop_front();
    if(c==-1) evaltop(); else { inwork[c]=0; evalc(c); }
    if(halted) break;
    if(!newfacts.empty()){ vector<pair<u32,u32>> nf; nf.swap(newfacts); for(auto&f:nf){ auto ws=topwait[f.first]; for(auto&n:ws) addtop(f.second&7,TW-1,n.win,f.second>>3); } }
    if((long)tab.n>MAXTOP){ limit=true; break; }
    if(!topst.empty()) push(-1); }
  size_t ncls=0; for(auto&u:U) if(!u.empty()) ncls++;
  printf("%s %c TW=%d K=%d : %s classes=%zu trans=%ld contracts=%ld facts=%ld top=%zu %.1fs %s\n",m,argv[2][0],TW,K, halted?"HALT-REACHABLE":(limit?"LIMIT":"NONHALT"),ncls,ntrans,ncontracts,nfacts,tab.n,chrono::duration<double>(chrono::steady_clock::now()-t0).count(),haltinfo.c_str());
  if(dump && !halted && !limit){ FILE*f=fopen(dump,"w"); fprintf(f,"machine %s %c\nwindow %d prefix %d\n",m,argv[2][0],TW,K);
    // classes are renumbered so that blank = 0
    auto id=[&](u32 q){ return q==1? 0u : q; };
    for(size_t r=0;r<U.size();r++) for(auto&x:U[r]) fprintf(f,"T %d %u %u\n",x.first,id(x.second),id(r));
    for(size_t c=0;c<Sum.size();c++) for(u32 x:Sum[c]) fprintf(f,"F %d %u %d %u\n",(int)(c%6),id(c/6),(int)(x&7),id(x>>3));
    string w(TW,'0'); for(size_t k=0;k<tab.t.size();k++) if(tab.used[k]){ auto&x=tab.t[k]; for(int j=0;j<TW;j++) w[j]='0'+((x.win>>j)&1); fprintf(f,"P %d %d %s %u\n",x.a,x.i,w.c_str(),id(x.q)); }
    fclose(f); }
  return halted?1:(limit?3:0); }
