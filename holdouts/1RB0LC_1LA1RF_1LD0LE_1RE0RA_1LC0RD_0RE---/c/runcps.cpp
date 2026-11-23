// runcps: a closed set of local configurations over runs of alternating cells (a CPS whose letters are runs).
// Each side of the head is the K maximal alternating runs nearest it (a run: its first bit and its length, exact
// below T, else ">= T" with its parity), plus a count of the runs beyond, capped at DM (environment, default 16).
// A step that uses up a run glues one back from the K-run windows seen so far on that side, as NGramCPS does with
// cells.  It starts from the configuration of the direct run at step START (whose windows are all recorded), and on
// a halt prints the derivation, each configuration marked real or UNREAL by the direct run up to step STEPS.
//   usage: runcps MACHINE K T MAXCONF STEPS START       e.g. DM=4 runcps M 4 6 20000000 3000000 1000000
// For 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE--- it fails: without the counts it reaches a halt by gluing the end of the
// tape where it is not; with them it does not close (90 million configurations, K 4, T 6, DM 4).
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>
#include <deque>
#include <unordered_set>
#include <unordered_map>
#include <string>
using namespace std;
typedef unsigned long long u64;
int K,T; int W_[6][2],D_[6][2],N_[6][2];
// token: 0 = E; else 1 + b*(T+1) + (lc-1), lc in 1..T+1 (T -> L0, T+1 -> L1)
static inline int tb(int t){return (t-1)/(T+1);} static inline int tl(int t){return (t-1)%(T+1)+1;}
static inline int mk(int b,int lc){return 1+b*(T+1)+lc-1;}
static inline int get(u64 S,int i){return (S>>(6*i))&63;}
static inline u64 setk(u64 S,int i,int t){return (S&~(63ULL<<(6*i)))|((u64)t<<(6*i));}
u64 MASK;
int DM=16; const u64 WM=(1ULL<<48)-1;
static inline int cnt(u64 S){ return (S>>48)&1023; }
static inline u64 withc(u64 w,int c){ return (w&WM)|((u64)c<<48); }
static inline u64 shl(u64 S,int t){ return (((S&WM)<<6)&MASK)|t; } // new nearest t, drop farthest
static inline u64 shr(u64 S){ return (S&WM)>>6; } // drop nearest; farthest slot becomes 0 (=E) placeholder
int inc(int lc){ if(lc==T) return T+1; if(lc==T+1) return T; return lc+1<T?lc+1:(T%2==0?T:T+1); }
struct H{size_t operator()(const pair<u64,u64>&p)const{return p.first*0x9E3779B97F4A7C15ULL^(p.second+0x7F4A7C15ULL*(p.first>>7));}};
struct Cfg{int q,h; u64 L,R;};
unordered_map<pair<u64,u64>,pair<u64,u64>,H> seen; pair<u64,u64> CUR{~0ULL,~0ULL}; deque<Cfg> todo;
unordered_set<u64> grams[2]; unordered_map<u64,vector<u64>> byp[2]; // prefix (K-1 tokens, near first) -> grams
unordered_map<u64,vector<u64>> waiters[2]; // prefix -> packed (q,h,other)
vector<u64> wother[2];
long long MAXC; bool halted=false; Cfg bad;
u64 pfx(u64 g){ return g & ((1ULL<<(6*(K-1)))-1); }
void add(int q,int h,u64 L,u64 R){ pair<u64,u64> k{L,R^((u64)(q*2+h)<<58)}; // q,h stored in high bits of R (R uses 6K<=54 bits)
  if(seen.emplace(k,CUR).second) todo.push_back({q,h,L,R}); }
void record(int side,u64 g){
  if(!grams[side].insert(g).second) return;
  u64 key=pfx(g); byp[side][key].push_back(g);
  auto it=waiters[side].find(key);
  if(it!=waiters[side].end()){ auto v=it->second; auto sv=CUR; if(get(g,K-1)==0) return; for(size_t i=0;i<v.size();i+=4){ int qh=v[i]&255; int c=v[i]>>8; u64 o=v[i+1]; int q=qh>>1,h=qh&1; CUR={v[i+2],v[i+3]};
      u64 G=withc(g,c); if(side==0) add(q,h,G,o); else add(q,h,o,G);} CUR=sv; }
}
u64 push(int side,u64 S,int c){
  int t=get(S,0);
  int cc=cnt(S); int nc=get(S,K-1)? (cc+1<DM?cc+1:DM) : cc;
  if(t==0){ if(c==0) return S; record(side,S&WM); return withc(shl(S,mk(1,1)),nc); }
  int b=tb(t),lc=tl(t);
  if(c!=b) return setk(S,0,mk(c,inc(lc)));
  record(side,S&WM); return withc(shl(S,mk(c,1)),nc);
}
// pops: output list of (bit, newS, needglue) ; when needglue newS holds the K-1 remaining tokens (prefix key)
struct P{int b; u64 S; bool g; int c;};
int pops(u64 S,P*out){
  int t=get(S,0); if(t==0){ out[0]={0,S,false}; return 1; }
  int b=tb(t),lc=tl(t); int n=0; int ds[2],nd=0; (void)0;
  if(lc==T){ ds[nd++]=T+1; if(T%2==0) ds[nd++]=T-1; }
  else if(lc==T+1){ ds[nd++]=T; if(T%2==1) ds[nd++]=T-1; }
  else ds[nd++]=lc-1;
  for(int i=0;i<nd;i++){ int m=ds[i];
    if(m==0){ u64 rem=shr(S); int cc=cnt(S);
      if(cc==0) out[n++]={b,rem,false,0};
      else { out[n++]={b,rem,true,cc==DM?DM:cc-1}; if(cc==DM) out[n++]={b,rem,true,DM-1}; }
    } else out[n++]={b,setk(S,0,mk(1-b,m)),false,cnt(S)};
  }
  return n;
}
void glue(int side,int q,int h,u64 o,u64 key,int c){
  auto &w=waiters[side][key]; w.push_back((u64)(q*2+h)|((u64)c<<8)); w.push_back(o); w.push_back(CUR.first); w.push_back(CUR.second);
  auto it=byp[side].find(key); if(it==byp[side].end()) return;
  auto v=it->second; for(u64 g:v){ if(get(g,K-1)==0) continue; u64 G=withc(g,c); if(side==0) add(q,h,G,o); else add(q,h,o,G);} }

unordered_set<pair<u64,u64>,H> realset;
u64 absside(const unsigned char*t,long long h,int dir,long long lo,long long hi){
  // canonical: from far end strip zeros; runs from head outward
  u64 S=0; long long p=h+dir; int i=0;
  // find far extent: last 1 in that direction
  long long far = dir>0? hi : lo; while((dir>0? far>=p : far<=p) && t[far]==0) far-=dir;
  while(i<K){
    if(dir>0? p>far : p<far){ break; }
    int b=t[p]; long long len=1; long long r=p+dir;
    while((dir>0? r<=far : r>=far) && t[r]!=t[r-dir]){ len++; r+=dir; }
    int lc = len<T? (int)len : T+(int)(len%2);
    S|=(u64)mk(b,lc)<<(6*i); i++; p=r;
  }
  int c=0;
  while(c<DM && (dir>0? p<=far : p>=far)){ long long r=p+dir; while((dir>0? r<=far : r>=far) && t[r]!=t[r-dir]) r+=dir; p=r; c++; }
  return withc(S,c);
}
long long START;
Cfg init; 
void allgrams(const unsigned char*t,long long h,int dir,long long lo,long long hi,int side){
  // full run list outward from head, then record every K-window
  vector<int> toks; long long p=h+dir;
  long long far = dir>0? hi : lo; while((dir>0? far>=p : far<=p) && t[far]==0) far-=dir;
  while(dir>0? p<=far : p>=far){ int b=t[p]; long long len=1; long long r=p+dir;
    while((dir>0? r<=far : r>=far) && t[r]!=t[r-dir]){ len++; r+=dir; }
    int lc = len<T? (int)len : T+(int)(len%2); toks.push_back(mk(b,lc)); p=r; }
  for(int i=0;i<K;i++) toks.push_back(0);
  for(size_t i=0;i+K<=toks.size();i++){ u64 g=0; for(int j=0;j<K;j++) g|=(u64)toks[i+j]<<(6*j); grams[side].insert(g); byp[side][pfx(g)].push_back(g); }
}
void runreal(const char*m,long long N){
  long long SZ=1<<26; unsigned char*t=(unsigned char*)calloc(SZ,1); long long h=SZ/2,lo=h,hi=h; int st=0;
  for(long long k=0;k<N;k++){
    if(k==START){ init={st,t[h],absside(t,h,-1,lo,hi),absside(t,h,1,lo,hi)}; allgrams(t,h,-1,lo,hi,0); allgrams(t,h,1,lo,hi,1); }
    if(k>=START){ u64 L=absside(t,h,-1,lo,hi), R=absside(t,h,1,lo,hi);
    realset.insert({L,R^((u64)(st*2+t[h])<<58)}); }
    int r=t[h]; int ns=N_[st][r]; if(ns<0) break; t[h]=W_[st][r]; h+=D_[st][r]; st=ns; if(h>hi)hi=h; if(h<lo)lo=h;
  }
}
int main(int argc,char**argv){
  const char*m=argv[1]; K=atoi(argv[2]); T=atoi(argv[3]); if(getenv("DM")) DM=atoi(getenv("DM")); MAXC=atoll(argv[4]);
  MASK=(K*6>=64)?~0ULL:((1ULL<<(6*K))-1);
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){const char*q=m+s*7+r*3; if(q[2]=='-'){N_[s][r]=-1;continue;} W_[s][r]=q[0]-'0';D_[s][r]=q[1]=='R'?1:-1;N_[s][r]=q[2]-'A';}
  START=atoll(argv[6]); runreal(m,atoll(argv[5])); fprintf(stderr,"real %zu\n",realset.size());
  add(init.q,init.h,init.L,init.R); long long proc=0;
  while(!todo.empty()){
    Cfg c=todo.front(); todo.pop_front(); proc++; CUR={c.L,c.R^((u64)(c.q*2+c.h)<<58)};
    int ns=N_[c.q][c.h]; if(ns<0){halted=true;bad=c;break;}
    int w=W_[c.q][c.h]; P out[4];
    if(D_[c.q][c.h]>0){ u64 L2=push(0,c.L,w); int n=pops(c.R,out);
      for(int i=0;i<n;i++){ if(!out[i].g) add(ns,out[i].b,L2,withc(out[i].S,out[i].c)); else glue(1,ns,out[i].b,L2,out[i].S,out[i].c);} }
    else { u64 R2=push(1,c.R,w); int n=pops(c.L,out);
      for(int i=0;i<n;i++){ if(!out[i].g) add(ns,out[i].b,withc(out[i].S,out[i].c),R2); else glue(0,ns,out[i].b,R2,out[i].S,out[i].c);} }
    if((long long)seen.size()>MAXC) break;
  }
  if(halted){ pair<u64,u64> k{bad.L,bad.R^((u64)(bad.q*2+bad.h)<<58)}; int n=0;
    while(n<400){ u64 L=k.first,R=k.second; int qh=R>>58; R&=(1ULL<<58)-1;
      printf("%c%d | L:",'A'+(qh>>1),qh&1); for(int i=0;i<K;i++){int t=get(L,i); if(!t)printf(" E"); else {int lc=tl(t); if(lc<T)printf(" %d:%d",tb(t),lc); else printf(" %d:L%d",tb(t),lc-T);}}
      printf(" | R:"); for(int i=0;i<K;i++){int t=get(R,i); if(!t)printf(" E"); else {int lc=tl(t); if(lc<T)printf(" %d:%d",tb(t),lc); else printf(" %d:L%d",tb(t),lc-T);}} printf(" %s\n", realset.count(k)?"real":"UNREAL");
      auto p=seen[k]; if(p.first==~0ULL){ printf("glue/start\n"); break;} k=p; n++; } }
  {size_t rc=0,miss=0; for(auto&k:realset){ if(seen.count(k)) rc++; else miss++;} printf("real-in-seen %zu real-missing %zu\n",rc,miss);}
  printf("%s K %d T %d configs %zu grams %zu %zu\n", halted?"HALT":(todo.empty()?"NONHALT":"LIMIT"),K,T,seen.size(),grams[0].size(),grams[1].size());
}
