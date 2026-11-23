// Exact block accelerator for a 2-symbol TM (used for 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC).
// Tape = two stacks of blocks (word, count), words stored outward from the head.
// 1. Crossing: when the head is about to enter an intact block w^k (k >= 2), a cached trial runs the machine on w^m
//    (m = 1..3) from the near edge; if the head leaves through the far edge in the state it entered with, the whole
//    block is crossed at once: floor(k/m) units become (w')^n on the other side, n*t steps.
// 2. Fronts: at each event (a copy split off a block) the configuration minus the counts of the two nearest blocks
//    with count >= 3 (the anchors) is a signature. When a signature recurs twice with the same count changes and
//    step count, with no crossing in between, and the second period never read deeper than u copies into an anchor,
//    the period is repeated as often as the shrinking anchor allows (keeping u+1 copies plus one period's worth).
// 3. Chunks of 64 literal cells crossed whole by a cached trial (see trychunk). Otherwise one cell at a time. Fresh cells are re-compressed into blocks. Trusted computation, not proved: checked
// against the plain simulator c/snap.c (py/tapecmp.py: tape, head and state equal) at 10^8 from blank tape and
// from snapshots 1e11->1.5e11, 2.5e11->3e11, 3e11->5e11, 4.99e11->5e11.
// usage: g++ -O2 -o bacc c/bacc.cpp
//        bacc MACHINE [-from SNAPFILE STEP] [-to T] [-every E] [-dump FILE] [-prof]
//   -from: start from a c/snap.c snapshot taken at step STEP; -every: print a block summary every E steps;
//   -dump: write the final tape in c/snap.c format ("0 head state", the tape); -ckpt FILE E: the same every E steps
//   (plus the step count on a third line), to restart with -from FILE STEP; prints HALT if the machine halts.
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64; typedef unsigned __int128 u128;
int W[6][2],MV[6][2],NX[6][2];
struct Blk{string w; u64 k; unsigned char lr=0; unsigned char m[21]={0};}; // lr, m: literal cells only (see pushcell)
vector<Blk> S[2]; // S[0]=left stack, S[1]=right stack
int cur, st; u128 steps=0;
struct TR{bool ok; string w2; u64 t;};
map<tuple<string,int,int>,TR> cache;
// side: 1 = entering right stack (outward = +R), 0 = left stack (outward = +L)
TR trial(const string& w,int q,int side){
  auto key=make_tuple(w,q,side); auto it=cache.find(key); if(it!=cache.end()) return it->second;
  string t=w; long p=0; int s=q; u64 n=0; TR r{false,"",0};
  long lim=200*(long)w.size()+2000;
  while(n<(u64)lim){
    int b=t[p]-'0'; if(NX[s][b]<0) break;
    t[p]='0'+W[s][b]; int d=MV[s][b]; if(side==0) d=-d; p+=d; s=NX[s][b]; n++;
    if(p<0) break;
    if(p>=(long)t.size()){ if(s==q){r.ok=true;r.w2=t;r.t=n;} break; }
  }
  cache[key]=r; return r;
}
static inline bool islit(const Blk&B){ return B.k==1 && B.w.size()==1; }
// A literal cell carries lr = length of the run of literal cells ending at it (from the far side, capped at 64) and
// m[p] = how many consecutive cells, starting at it and going away from the head, equal the cell p further away
// (within the literal run). Both depend only on the cells below it, so they never change while it sits in the stack.
static void pushcell(int side,int c){
  vector<Blk>&V=S[side];
  Blk nb; nb.w=string(1,'0'+c); nb.k=1;
  size_t n0=V.size();
  bool below_lit = n0>0 && islit(V[n0-1]);
  nb.lr = below_lit ? (unsigned char)min(64,V[n0-1].lr+1) : 1;
  for(int p=1;p<=20;p++){
    if(nb.lr>p && V[n0-p].w[0]=='0'+c){ int prev = (n0>=1 && islit(V[n0-1])) ? V[n0-1].m[p] : 0; nb.m[p]=(unsigned char)min(64,prev+1); }
    else nb.m[p]=0;
  }
  V.push_back(nb);
  int lit=nb.lr;
  // absorb: the literal run (exactly p cells) equals the word of the block below it
  if(lit<(int)V.size() && lit<64){
    Blk&B=V[V.size()-1-lit]; int p=B.w.size();
    if(p==lit && (B.k>1||p>1)){
      bool eq=true; for(int i=0;i<p;i++){ if(V[V.size()-lit+ (p-1-i)].w[0]!=B.w[i]){eq=false;break;} }
      if(eq){ B.k++; V.resize(V.size()-p); return; }
    }
  }
  if(lit>=24){
    const Blk&T=V.back();
    for(int p=1;p<=20;p++){
      int run=min((int)T.m[p]+p, lit); int reps=run/p;
      if(reps*p>=24 && reps>=3){
        string w; for(int i=0;i<p;i++) w+=V[V.size()-1-i].w[0];
        V.resize(V.size()-reps*p);
        if(!V.empty() && V.back().w==w) V.back().k+=reps; else { Blk B; B.w=w; B.k=reps; V.push_back(B); }
        return;
      }
    }
  }
}
bool splitev=false;
static void pushlit(int side,int c){ // a literal without compression (cells of a split copy)
  vector<Blk>&V=S[side]; Blk nb; nb.w=string(1,'0'+c); nb.k=1; size_t n0=V.size();
  nb.lr = (n0>0 && islit(V[n0-1])) ? (unsigned char)min(64,V[n0-1].lr+1) : 1;
  for(int p=1;p<=20;p++){ if(nb.lr>p && V[n0-p].w[0]=='0'+c){ int prev=(n0>=1&&islit(V[n0-1]))?V[n0-1].m[p]:0; nb.m[p]=(unsigned char)min(64,prev+1);} else nb.m[p]=0; }
  V.push_back(nb);
}
void track_pop(int side,size_t idx_after);
static int popcell(int side){
  vector<Blk>&V=S[side]; if(V.empty()) return 0;
  Blk&B=V.back();
  if(B.k==1 && B.w.size()==1){ int c=B.w[0]-'0'; V.pop_back(); track_pop(side,0); return c; }
  // split one copy off: copy cells outward w[0..p-1]; head takes w[0], rest pushed as literals so that w[1] is top
  string w=B.w; splitev=true; if(--B.k==0) V.pop_back(); track_pop(side,0);
  for(int i=(int)w.size()-1;i>=1;i--) pushlit(side,w[i]-'0');
  return w[0]-'0';
}
u128 TO=(u128)-1;
u64 jumps_fwd; u64 jumps=0, lits=0; bool PROF=false;
void ctx(){ fprintf(stderr,"ctx st %c cur %d | L:",'A'+st,cur); for(int i=0;i<6&&i<(int)S[0].size();i++){auto&B=S[0][S[0].size()-1-i]; fprintf(stderr," %s^%llu",B.w.c_str(),B.k);} fprintf(stderr," | R:"); for(int i=0;i<6&&i<(int)S[1].size();i++){auto&B=S[1][S[1].size()-1-i]; fprintf(stderr," %s^%llu",B.w.c_str(),B.k);} fprintf(stderr,"\n"); }

// ---- translated-cycle (front) acceleration ----
u64 cycj=0; u128 cycsteps=0;
struct Cand{ bool on=false; string sig; long ai[2]; u64 c0[2]; u128 s0; u64 j0; long long d[2]; u128 t; u64 mn[2]; bool bad=false; int seen=0; };
Cand C;
unordered_map<string,tuple<u128,u64,u64,u64>> seenmap; // sig -> steps, jumps, cL, cR
bool anchors(long ai[2]){
  for(int sd=0;sd<2;sd++){ auto&V=S[sd]; long i=(long)V.size()-1, lim=max(0L,(long)V.size()-40); ai[sd]=-1;
    for(;i>=lim;i--) if(V[i].k>=3){ai[sd]=i;break;} if(ai[sd]<0) return false; }
  return true;
}
string mksig(long ai[2]){
  string g; g+=char('A'+st); g+=char('0'+cur);
  for(int sd=0;sd<2;sd++){ auto&V=S[sd]; g+='|'; g+=to_string(ai[sd]); g+=':'; g+=V[ai[sd]].w;
    for(long i=ai[sd]+1;i<(long)V.size();i++){ g+=','; g+=V[i].w; g+='^'; g+=to_string(V[i].k);} }
  return g;
}
void track_pop(int side,size_t idx_after){ // called when a block at index idx is decremented / popped
  if(!C.on) return;
  long ai=C.ai[side];
  if((long)S[side].size()<=ai){ C.bad=true; return; }
  if((long)S[side].size()-1==ai){ u64 k=S[side][ai].k; if(k<C.mn[side]) C.mn[side]=k; }
}
void on_event(){
  long ai[2]; if(!anchors(ai)) { C.on=false; return; }
  string g=mksig(ai);
  u64 cL=S[0][ai[0]].k, cR=S[1][ai[1]].k;
  if(C.on){
    if(C.bad || jumps!=C.j0 || steps-C.s0>(u128)20000000){ C.on=false; }
    else if(g==C.sig){
      long long dL=(long long)cL-(long long)C.c0[0], dR=(long long)cR-(long long)C.c0[1]; u128 t=steps-C.s0;
      if(dL==C.d[0] && dR==C.d[1] && t==C.t && (dL||dR)){
        u64 uL=C.c0[0]-min(C.mn[0],C.c0[0]), uR=C.c0[1]-min(C.mn[1],C.c0[1]);
        u64 n=(u64)-1; long long dd[2]={dL,dR}; u64 cc[2]={cL,cR}, uu[2]={uL,uR};
        for(int sd=0;sd<2;sd++) if(dd[sd]<0){ u64 need=uu[sd]+1+(u64)(-dd[sd]); u64 room = cc[sd]>need ? cc[sd]-need : 0; n=min(n, room/(u64)(-dd[sd])); }
        if(n==(u64)-1) n=0; // both growing: no jump (no natural end)
        if(TO!=(u128)-1){ u128 room=TO-steps; u64 nm=(u64)(room/t); if(nm<n) n=nm; }
        if(n>=1){ S[0][ai[0]].k=cL+dL*(long long)n; S[1][ai[1]].k=cR+dR*(long long)n; steps+=(u128)n*t; cycj++; cycsteps+=(u128)n*t;
          cL=S[0][ai[0]].k; cR=S[1][ai[1]].k; g=mksig(ai); }
      }
      C.d[0]=dL; C.d[1]=dR; C.t=t;
      C.bad=false; C.c0[0]=cL; C.c0[1]=cR; C.s0=steps; C.mn[0]=cL; C.mn[1]=cR; C.sig=g;
      return;
    } else return; // another event inside the period
  }
  auto it=seenmap.find(g);
  if(it!=seenmap.end()){
    auto [s0,j0,l0,r0]=it->second;
    if(j0==jumps && steps-s0<(u128)20000000 && (cL!=l0||cR!=r0)){
      C.on=true; C.bad=false; C.sig=g; C.ai[0]=ai[0]; C.ai[1]=ai[1]; C.d[0]=(long long)cL-(long long)l0; C.d[1]=(long long)cR-(long long)r0;
      C.t=steps-s0; C.c0[0]=cL; C.c0[1]=cR; C.s0=steps; C.j0=jumps; C.mn[0]=cL; C.mn[1]=cR; seenmap.clear(); return;
    }
  }
  if(seenmap.size()>200000) seenmap.clear();
  seenmap[g]=make_tuple(steps,jumps,cL,cR);
}

// 3. Chunks: when at least CH literal cells lie ahead, a cached trial runs the machine on those CH cells from the
//    near edge; if the head leaves through the far edge (in any state), the chunk is replaced in one go.
const int CH=64;
struct TR2{bool ok; string w2; u64 t; int q2;};
unordered_map<string,TR2> cache2; u64 chunkj=0;
TR2 trial2(const string& w,int q,int side){
  string key=w; key+=char('A'+q); key+=char('0'+side);
  auto it=cache2.find(key); if(it!=cache2.end()) return it->second;
  string t=w; long p=0; int s=q; u64 n=0; TR2 r{false,"",0,0};
  while(n<200000){
    int b=t[p]-'0'; if(NX[s][b]<0) break;
    t[p]='0'+W[s][b]; int d=MV[s][b]; if(side==0) d=-d; p+=d; s=NX[s][b]; n++;
    if(p<0) break;
    if(p>=(long)t.size()){ r.ok=true; r.w2=t; r.t=n; r.q2=s; break; }
  }
  if(cache2.size()>1000000) cache2.clear();
  cache2[key]=r; return r;
}
bool trychunk(int to,int fr){
  vector<Blk>&V=S[to]; if(V.size()<(size_t)CH || V.back().lr<CH) return false;
  string w(CH,'0'); for(int i=0;i<CH;i++) w[i]=V[V.size()-1-i].w[0];
  TR2 r=trial2(w,st,to); if(!r.ok) return false;
  if(TO!=(u128)-1 && steps+r.t>TO) return false;
  V.resize(V.size()-CH);
  for(int i=0;i<CH;i++) pushcell(fr,r.w2[i]-'0');
  st=r.q2; steps+=r.t; chunkj++; return true;
}
bool step(){
  int b=cur; int nx=NX[st][b]; if(nx<0) return false;
  int d=MV[st][b]; int to=(d>0)?1:0, fr=1-to;
  pushcell(fr,W[st][b]); st=nx; steps++; lits++; if(PROF && lits%2000000==0) ctx();
  // acceleration into S[to]
  for(;;){
    vector<Blk>&V=S[to]; if(V.empty()) break; Blk&B=V.back(); if(B.k<2) break;
    bool done=false, capped=false;
    for(int m=1;m<=3 && !done;m++){
      if(B.k<(u64)m*2) break;
      string wm; for(int i=0;i<m;i++) wm+=B.w;
      TR r=trial(wm,st,to); if(!r.ok) continue;
      u64 n=B.k/m; if(TO!=(u128)-1){ u128 room=TO-steps; u64 nmax=(u64)(room/r.t); if(nmax<n) n=nmax; }
      if(n<1) { capped=true; break; }
      string w2=r.w2; reverse(w2.begin(),w2.end()); // in other stack's outward order
      // w2 currently: tape region crossed, in 'to' outward order of m copies; reversed => outward for fr side, but per unit
      B.k-=n*m; string W2=w2; if(B.k==0) V.pop_back();
      vector<Blk>&O=S[fr]; if(!O.empty()&&O.back().w==W2) O.back().k+=n; else { Blk nb; nb.w=W2; nb.k=n; O.push_back(nb); }
      steps+=(u128)n*r.t; jumps++; done=true;
    }
    if(!done || capped) break;
    // after a jump, maybe next block also crossable: loop
    if(TO!=(u128)-1 && steps>=TO) break;
  }
  { bool any=false; while(trychunk(to,fr)) any=true; if(any){ C.on=false; jumps++; } }
  splitev=false; cur=popcell(to); if(splitev){ splitev=false; on_event(); }
  return true;
}
string tapestr(long &head){ // full tape string and head index
  string L,R; for(auto&B:S[0]) { string s; for(u64 i=0;i<B.k;i++) s+=B.w; L+=s; } // L outward order from far? S[0][0] is farthest
  // S[0] vector: index 0 = farthest from head; each word outward (w[0] nearest head) -> tape order = reverse
  string left; for(size_t i=0;i<S[0].size();i++){ string w=S[0][i].w; reverse(w.begin(),w.end()); for(u64 j=0;j<S[0][i].k;j++) left+=w; }
  string right; for(size_t i=S[1].size();i-->0;){ for(u64 j=0;j<S[1][i].k;j++) right+=S[1][i].w; }
  head=left.size(); return left+string(1,'0'+cur)+right;
}
string pr128(u128 x){ string s; if(!x) return "0"; while(x){s+=char('0'+x%10);x/=10;} reverse(s.begin(),s.end()); return s;}
void summary(FILE*f){
  // blocks along the tape from left to right, compressing literal runs to ~n
  fprintf(f,"cyc %llu/%s step %s state %c jumps %llu blocks %zu+%zu ::",(unsigned long long)cycj,pr128(cycsteps).c_str(),pr128(steps).c_str(),'A'+st,jumps,S[0].size(),S[1].size());
  long lit=0;
  auto flush=[&](){ if(lit){fprintf(f," ~%ld",lit);lit=0;} };
  for(size_t i=0;i<S[0].size();i++){ auto&B=S[0][i]; if(B.w.size()*B.k>=600){flush(); string w=B.w; reverse(w.begin(),w.end()); fprintf(f," (%s)^%llu",w.c_str(),B.k);} else lit+=B.w.size()*B.k; }
  flush(); fprintf(f," [%c>%d]",'A'+st,cur);
  for(size_t i=S[1].size();i-->0;){ auto&B=S[1][i]; if(B.w.size()*B.k>=600){flush(); fprintf(f," (%s)^%llu",B.w.c_str(),B.k);} else lit+=B.w.size()*B.k; }
  flush(); fprintf(f,"\n"); fflush(f);
}
int main(int argc,char**argv){
  const char*m=argv[1];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*t=m+s*7+b*3;if(t[0]=='-'){NX[s][b]=-1;continue;}W[s][b]=t[0]-'0';MV[s][b]=t[1]=='R'?1:-1;NX[s][b]=t[2]-'A';}
  const char*dump=0,*ck=0; u128 every=0, ckev=0; cur=0; st=0;
  for(int i=2;i<argc;i++){ string a=argv[i];
    if(a=="-prof") PROF=true; else if(a=="-to") TO=(u128)strtold(argv[++i],0);
    else if(a=="-dump") dump=argv[++i];
    else if(a=="-ckpt"){ ck=argv[++i]; ckev=(u128)strtold(argv[++i],0); }
    else if(a=="-every") every=(u128)strtold(argv[++i],0);
    else if(a=="-from"){ FILE*f=fopen(argv[++i],"r"); long L,P; char c; fscanf(f,"%ld %ld %c",&L,&P,&c); static char buf[1<<25]; fscanf(f,"%s",buf); fclose(f);
      steps=(u128)strtold(argv[++i],0); st=c-'A'; long h=P-L; string t=buf; cur=t[h]-'0';
      for(long j=0;j<h;j++) pushcell(0,t[j]-'0');
      for(long j=(long)t.size()-1;j>h;j--) pushcell(1,t[j]-'0'); }
  }
  u128 next=every?((steps/every)+1)*every:0; u128 cnext=ckev?((steps/ckev)+1)*ckev:0;
  auto writeck=[&](const char*fn){ long h; string t=tapestr(h); string tmp=string(fn)+".tmp"; FILE*f=fopen(tmp.c_str(),"w"); fprintf(f,"0 %ld %c\n%s\n%s\n",h,'A'+st,t.c_str(),pr128(steps).c_str()); fclose(f); rename(tmp.c_str(),fn); };
  u128 T=TO;
  while(true){
    if(T!=(u128)-1 && steps>=T) break;
    if(ckev && steps>=cnext){ writeck(ck); cnext=(steps/ckev+1)*ckev; }
    if(every && steps>=next){ summary(stdout); next=(steps/every+1)*every; }
    if(!step()){ printf("HALT at step %s state %c\n",pr128(steps+1).c_str(),'A'+st); summary(stdout); return 0; }
  }
  summary(stdout);
  if(dump){ long h; string t=tapestr(h); FILE*f=fopen(dump,"w"); fprintf(f,"0 %ld %c\n%s\n",h,'A'+st,t.c_str()); fclose(f); }
}
