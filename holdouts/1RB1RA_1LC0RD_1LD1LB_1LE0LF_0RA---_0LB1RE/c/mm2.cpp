// mm2.cpp: exact macro simulator for a two-symbol machine: blocks of K cells, two-block windows, chain steps.
//
// Tape = two stacks of runs (block, count), left and right of the head, with the head at the junction of their tops,
// moving in direction d. A macro step simulates the machine cell by cell on the window [block behind][block in front]
// from the junction until the head leaves the window (results memoised). A zigzag across the junction is inside the
// window, so sweeps that step back one cell per copy of a word still chain: if the head leaves the window forward in
// the same state and the front block became the old behind block (b -> y, y -> z), then every copy in the front run
// does the same (induction on copies) and the run is replaced in one step: [y | b^n] -> [z^n y |], n times the steps.
// Everything is exact (no extrapolation); a halt inside a window is reported.
// On 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE it matches direct simulation at 3 checkpoints with K = 15 and 6 with K = 30, up to
// 3e9 steps (whole tape, state and head compared with a direct simulator) and runs 2 to 4 times faster than direct
// simulation up to 3e11 steps; the irregular digit list, which most visits cross, does not compress.
//
// usage: mm2 MACHINE K LOG10MAX [DUMP_STEPS...]   progress lines every x1.25 steps; DUMP prints the whole tape
// build: g++ -O2 -std=c++17 -o mm2 mm2.cpp
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64; typedef unsigned __int128 u128;
int K; int W[8][2],MV[8][2],NX[8][2];
struct Res{ u64 y2,b2; int ns, fwd; u64 steps; int halt; };
struct Key{ u64 y,b; int sd; bool operator==(const Key&o)const{return y==o.y&&b==o.b&&sd==o.sd;} };
struct KH{ size_t operator()(const Key&k)const{ u64 h=k.y*0x9E3779B97F4A7C15ULL; h^=(h>>29); h+=k.b*0xC2B2AE3D27D4EB4FULL; h^=(h>>31); return h+k.sd*0x165667B19E3779F9ULL; } };
unordered_map<Key,Res,KH> memo;
// window cells: for d=+1: cells 0..K-1 = y (left), K..2K-1 = b; head starts at K moving right.
// for d=-1: cells 0..K-1 = b (left), K..2K-1 = y; head starts at K-1.
Res compute(u64 y,u64 b,int s,int d){
  unsigned char c[128]; u64 L= d>0? y:b, R= d>0? b:y;
  for(int i=0;i<K;i++){ c[i]=(L>>i)&1; c[K+i]=(R>>i)&1; }
  int p= d>0? K : K-1; u64 st=0;
  while(p>=0&&p<2*K){
    int x=c[p]; if(NX[s][x]<0) return Res{0,0,s,0,st,1};
    c[p]=W[s][x]; int m=MV[s][x]; s=NX[s][x]; p+=m; st++;
    if(st>100000000ULL){ fprintf(stderr,"window loop\n"); exit(2);}
  }
  u64 nl=0,nr=0; for(int i=0;i<K;i++){ nl|=(u64)c[i]<<i; nr|=(u64)c[K+i]<<i; }
  int exitright = p>=2*K; int fwd = (exitright == (d>0));
  Res r; r.halt=0; r.steps=st; r.ns=s; r.fwd=fwd;
  if(d>0){ r.y2=nl; r.b2=nr; } else { r.y2=nr; r.b2=nl; }
  return r;
}
struct Run{u64 b; u64 n;};
vector<Run> Ls,Rs;
inline void push(vector<Run>&S,u64 b,u64 n){ if(!S.empty()&&S.back().b==b) S.back().n+=n; else S.push_back({b,n}); }
string blk(u64 b){ string s; for(int i=0;i<K;i++) s+=char('0'+((b>>i)&1)); return s; }
int main(int argc,char**argv){
  string m=argv[1]; K=atoi(argv[2]); double lmax=atof(argv[3]);
  int NS=0; for(size_t g=0; g<m.size(); g+=7){ for(int r=0;r<2;r++){ string t=m.substr(g+3*r,3); if(t[0]=='-'){NX[NS][r]=-1;} else {W[NS][r]=t[0]-'0';MV[NS][r]=t[1]=='R'?1:-1;NX[NS][r]=t[2]-'A';} } NS++; }
  vector<long double> dumps; for(int i=4;i<argc;i++) dumps.push_back(atof(argv[i])); size_t di=0;
  u128 steps=0; int s=0,d=1; u64 macro=0,nch=0; long double maxsteps=powl(10.0L,lmax);
  long double nextrep=1e6; auto t0=chrono::steady_clock::now();
  Ls.push_back({0,1});
  while(true){
    vector<Run>&F = d>0?Rs:Ls; vector<Run>&B = d>0?Ls:Rs;
    if(F.empty()) F.push_back({0,1});
    if(B.empty()) B.push_back({0,1});
    u64 b=F.back().b, y=B.back().b;
    Key k{y,b,s*2+(d>0)}; auto it=memo.find(k); Res r;
    if(it==memo.end()){ r=compute(y,b,s,d); if(memo.size()>40000000) memo.clear(); memo[k]=r; } else r=it->second;
    if(r.halt){ printf("HALT near step %.6Le\n",(long double)steps); return 0;}
    if(r.fwd && r.ns==s && r.b2==y){ u64 n=F.back().n; F.pop_back(); if(--B.back().n==0) B.pop_back(); push(B,r.y2,n); push(B,y,1); steps+=(u128)r.steps*n; nch++; }
    else {
      // remove y (one copy) from B and b (one copy) from F
      if(--B.back().n==0) B.pop_back(); if(--F.back().n==0) F.pop_back();
      if(r.fwd){ push(B,r.y2,1); push(B,r.b2,1); }   // head now beyond b2, same direction
      else { push(F,r.b2,1); push(F,r.y2,1); d=-d; } // head left the window behind y: now moving the other way
      s=r.ns; steps+=r.steps;
    }
    long double ls=(long double)steps;
    if(ls>=nextrep){ double el=chrono::duration<double>(chrono::steady_clock::now()-t0).count();
      u64 cl=0,cr=0; for(auto&x:Ls) cl+=x.n; for(auto&x:Rs) cr+=x.n;
      printf("%8.1fs steps %.4Le (10^%.3Lf) macro %llu chain %llu runs %zu+%zu blocks %llu+%llu memo %zu\n",el,ls,log10l(ls),(unsigned long long)macro,(unsigned long long)nch,Ls.size(),Rs.size(),(unsigned long long)cl,(unsigned long long)cr,memo.size()); fflush(stdout);
      nextrep*=1.25; }
    if(di<dumps.size() && ls>=dumps[di]){
      string tape; for(auto&x:Ls) for(u64 i=0;i<x.n;i++) tape+=blk(x.b); long long hp=tape.size();
      for(int i=(int)Rs.size()-1;i>=0;i--) for(u64 j=0;j<Rs[i].n;j++) tape+=blk(Rs[i].b);
      printf("DUMP %.0Lf %c %d %lld %s\n", ls, 'A'+s, d, hp, tape.c_str()); di++; }
    if(ls>maxsteps) break;
  }
}
