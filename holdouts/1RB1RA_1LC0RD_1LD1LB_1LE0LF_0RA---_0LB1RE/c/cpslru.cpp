// cpslru: search for a closed tape language with the CPS_LRU abstraction of busycoq's CTL.v (our own implementation).
//
//   cpslru MACHINE SIM_STEPS MAX_STATES START DUMP|- SPEC...        SPEC = BSZ,LEN1,LEN2,LRU_N
//
// The machine is run SIM_STEPS steps from blank tape in state START (A..F).  From the configuration reached, the
// tape is cut into blocks of BSZ cells and each side of the head is summarised, far end first, by the LEN1 blocks
// nearest the head followed by the list of at most LEN2 different blocks seen beyond them, most recently seen
// first (the LRU_N-th earlier copy of a block is dropped when it comes round again; busycoq's `upd_skipn_LRU`).
// A set of abstract configurations (state, direction, left summary, right summary) is grown until it is closed
// under the machine's block steps.  Output per SPEC: CLOSED (no halting step is possible from the set, so the
// machine never halts after SIM_STEPS), halt (a halting step is possible from the set: nothing follows), toobig
// (more than MAX_STATES summaries or 20*MAX_STATES configurations), blocktimeout.
//
// This is a search program, not a proof: nothing here is checked by Lean or Coq.  It reproduces busycoq's
// `CPS_LRU 100000001 400000 400000 8 3200 2 6 0 0` for 1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1LB (CLOSED with 4,035
// configurations) and was used in round 6 to try the same on this folder's machine (see README).
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;
int W[6][2],D[6][2],N[6][2]; bool Hlt[6][2];
int bsz,len1,len2,LRUn; long maxS;
struct VH{size_t operator()(const vector<int>&v)const{size_t h=1469598103934665603ULL;for(int x:v){h^=(unsigned)x;h*=1099511628211ULL;}return h;}};
struct Side{
  unordered_map<vector<int>,int,VH> id; vector<vector<int>> st;
  vector<vector<pair<int,int>>> preds; // preds[X] = (X',y)
  vector<unordered_set<u64>> pset;
  int get(const vector<int>&v){auto it=id.find(v);if(it!=id.end())return it->second;int k=st.size();id[v]=k;st.push_back(v);preds.emplace_back();pset.emplace_back();return k;}
  int trans(int X,int y){
    const vector<int>&x=st[X];
    if(x.empty()&&y==0)return X;
    vector<int> r; r.reserve(x.size()+1);
    r.push_back(y); for(int a:x)r.push_back(a);
    if((int)r.size()>len1){
      // LRU on r[len1:]
      int h=r[len1]; vector<int> t; t.push_back(h); int n=LRUn; bool removed=false;
      for(size_t i=len1+1;i<r.size();i++){ if(!removed&&r[i]==h){ if(n==0){removed=true;continue;} n--; } t.push_back(r[i]); }
      if((int)t.size()>len2)t.resize(len2);
      r.resize(len1); for(int a:t)r.push_back(a);
    }
    return get(r);
  }
  bool addpred(int X,int Xp,int y){u64 k=((u64)Xp<<20)|y; if(pset[X].insert(k).second){preds[X].push_back({Xp,y});return true;}return false;}
};
Side S[2]; // 0 = left, 1 = right
// block: bit i = cell i (left to right)
// macro step: enter from left (dir=1, moving right) or from right (dir=0). returns 0 exit left,1 exit right,2 halt,3 timeout
int bmaxT=3200; long micrototal=0;
int macro(int q,int dir,int y,int&q2,int&y2){
  int pos=dir?0:bsz-1; int t=0;
  while(true){
    int b=(y>>pos)&1; if(Hlt[q][b])return 2;
    y=(y&~(1<<pos))|(W[q][b]<<pos); int d=D[q][b]; q=N[q][b]; pos+=d?1:-1; t++; micrototal++;
    if(pos<0){q2=q;y2=y;return 0;} if(pos>=bsz){q2=q;y2=y;return 1;}
    if(t>bmaxT)return 3;
  }
}
struct Cfg{int q,dir,L,R;};
struct CH{size_t operator()(const array<int,4>&a)const{return ((size_t)a[0]*1000003u+a[1])*1000003u*1000003u ^ ((size_t)a[2]*2654435761u) ^ ((size_t)a[3]*40503u*65537u);}};
unordered_set<array<int,4>,CH> seen; vector<array<int,4>> cfgs;
vector<vector<int>> facing[2]; // facing[side][X] = cfg indices
deque<pair<int,int>> work; // (cfg index, pred index start) -> process all preds from given index
vector<int> done; // number of preds processed per cfg
int fail=0;
void addcfg(int q,int dir,int L,int R){
  array<int,4> a={q,dir,L,R}; if(!seen.insert(a).second)return;
  int k=cfgs.size(); cfgs.push_back(a); done.push_back(0);
  int side=dir, X=dir?R:L; if((int)facing[side].size()<=X)facing[side].resize(X+1);
  facing[side][X].push_back(k); work.push_back({k,0});
}
void notify(int side,int X){ if((int)facing[side].size()>X) for(int k:facing[side][X]) work.push_back({k,0}); }
void regpred(int side,int X,int Xp,int y){ if(S[side].addpred(X,Xp,y)) notify(side,X); }

vector<char> tape; long tpos,tlo,thi; int tq;
int runone(const string&m,long simT,const char*dump){
  S[0]=Side();S[1]=Side();seen.clear();cfgs.clear();facing[0].clear();facing[1].clear();work.clear();done.clear();fail=0;micrototal=0;
  int nilL=S[0].get({}),nilR=S[1].get({}); S[0].addpred(nilL,nilL,0); S[1].addpred(nilR,nilR,0);
  { long pos=tpos,lo=tlo,hi=thi; int q=tq;
    int L=nilL; { long n=pos-lo; long nb=(n+bsz-1)/bsz; for(long k=nb-1;k>=0;k--){
        int y=0; for(int i=0;i<bsz;i++){long c=pos-(k+1)*bsz+i; if(c>=lo&&tape[c])y|=1<<i;} int L2=S[0].trans(L,y); S[0].addpred(L2,L,y); L=L2; } }
    int R=nilR; { long n=hi-pos+1; long nb=(n+bsz-1)/bsz; for(long k=nb-1;k>=0;k--){ int y=0; for(int i=0;i<bsz;i++){long c=pos+k*bsz+i; if(c<=hi&&tape[c])y|=1<<i;} int R2=S[1].trans(R,y); S[1].addpred(R2,R,y); R=R2; } }
    addcfg(q,1,L,R);
  }
  while(!work.empty()){
    auto [k,dummy]=work.front(); work.pop_front();
    array<int,4> a=cfgs[k]; int q=a[0],dir=a[1],L=a[2],R=a[3]; int side=dir; int X=dir?R:L;
    while(done[k]<(int)S[side].preds[X].size()){
      auto [Xp,y]=S[side].preds[X][done[k]]; done[k]++;
      int q2,y2; int r=macro(q,dir,y,q2,y2);
      if(r==2){fail=1; goto out;} if(r==3){fail=2; goto out;}
      int os=1-side; int O=dir?L:R;
      if(r==dir){ int O2=S[os].trans(O,y2); regpred(os,O2,O,y2);
        if(dir) addcfg(q2,1,O2,Xp); else addcfg(q2,0,Xp,O2);
      } else { int X2=S[side].trans(Xp,y2); regpred(side,X2,Xp,y2);
        if(dir) addcfg(q2,0,L,X2); else addcfg(q2,1,X2,R); }
      if((long)(S[0].st.size()+S[1].st.size())>maxS || (long)cfgs.size()>20*maxS){fail=3; goto out;}
    }
  }
  out:
  long np=0; for(int s=0;s<2;s++)for(auto&p:S[s].preds)np+=p.size();
  printf("%s bsz=%d len1=%d len2=%d LRU=%d simT=%ld: %s cfgs=%zu statesL=%zu statesR=%zu preds=%ld micro=%ld\n",m.c_str(),bsz,len1,len2,LRUn,simT,fail==0?"CLOSED":fail==1?"halt":fail==2?"blocktimeout":"toobig",cfgs.size(),S[0].st.size(),S[1].st.size(),np,micrototal); fflush(stdout);
  if(dump&&!fail){ FILE*f=fopen(dump,"w"); fprintf(f,"%d %d %d %d %d\n",bsz,cfgs[0][0],cfgs[0][1],cfgs[0][2],cfgs[0][3]);
    for(int s=0;s<2;s++){ long n=0; for(auto&p:S[s].preds)n+=p.size(); fprintf(f,"%zu %ld\n",S[s].st.size(),n); for(size_t X=0;X<S[s].st.size();X++)for(auto&p:S[s].preds[X])fprintf(f,"%zu %d %d\n",X,p.first,p.second); }
    fprintf(f,"%zu\n",cfgs.size()); for(auto&a:cfgs)fprintf(f,"%d %d %d %d\n",a[0],a[1],a[2],a[3]); fclose(f); }
  return fail;
}
// usage: cps MACHINE simT maxS start dumpfile|- spec...   spec = bsz,len1,len2,lru
int main(int argc,char**argv){
  string m=argv[1]; long simT=atol(argv[2]); maxS=atol(argv[3]); int q0=argv[4][0]-'A'; const char*dump=strcmp(argv[5],"-")?argv[5]:0;
  for(int i=0;i<6;i++)for(int b=0;b<2;b++){const char*t=m.c_str()+i*7+b*3; if(t[0]=='-'){Hlt[i][b]=1;}else{W[i][b]=t[0]-'0';D[i][b]=t[1]=='R';N[i][b]=t[2]-'A';}}
  long sz=1<<27; tape.assign(sz,0); long pos=sz/2,lo=pos,hi=pos; int q=q0;
  for(long t=0;t<simT;t++){int b=tape[pos]; if(Hlt[q][b]){printf("HALT in sim at %ld\n",t);return 1;} tape[pos]=W[q][b]; int d=D[q][b]; q=N[q][b]; pos+=d?1:-1; if(pos<lo)lo=pos; if(pos>hi)hi=pos; if(pos<8||pos>sz-8){printf("tape overflow\n");return 1;}}
  tpos=pos;tlo=lo;thi=hi;tq=q; fprintf(stderr,"sim done width %ld\n",hi-lo);
  int ok=1;
  for(int i=6;i<argc;i++){ sscanf(argv[i],"%d,%d,%d,%d",&bsz,&len1,&len2,&LRUn); if(runone(m,simT,dump)==0){ok=0; if(dump)break;} }
  return ok;
}
