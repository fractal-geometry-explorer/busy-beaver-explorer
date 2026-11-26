// cps MACHINE MASK12 NL NR T [MAXCONF] : n-gram CPS started from the configuration the machine reaches after T steps
// from blank tape; slots marked '*' in MASK (and '---') count as halting.  Prints NONHALT / HALTREACH / LIMIT.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <string>
using namespace std;
typedef uint64_t u64;
int w[12],mv[12],ns[12]; bool bad[12];
int NL,NR; int bst=-1,bh=0,bside=1,bn=0;
struct K{u64 a;u64 b; bool operator==(const K&o)const{return a==o.a&&b==o.b;}};
struct KH{size_t operator()(const K&k)const{return k.a*0x9E3779B97F4A7C15ULL^(k.b+0x7F4A7C15)*0xC2B2AE3D27D4EB4FULL;}};
// left window: bit i = cell at distance i+1 from head (i<NL). same for right.
unordered_set<u64> G[2]; // full n-grams
unordered_map<u64,int> P[2]; // prefix (n-1 nearest... ) see below -> mask of far symbol
unordered_map<u64,vector<K>> W[2]; // waiters by prefix
unordered_set<K,KH> C; vector<K> work;
static inline K mk(int s,int h,u64 l,u64 r){return K{l,(r<<4)|(u64)(s<<1|h)};}
void addC(K k){ if(C.insert(k).second) work.push_back(k); }
// gram on side d: bits 0..n-1, bit0 nearest. "tail" t = bits 1..n-1 of the *new* window = (gram>>... ) we key by the n-1 nearest cells, value far cell
void addG(int d,u64 g){ int n=d?NR:NL; if(!G[d].insert(g).second) return; u64 pre=g&((1ULL<<(n-1))-1); int far=(g>>(n-1))&1; int &m=P[d][pre]; if(!(m>>far&1)){ m|=1<<far; auto it=W[d].find(pre); if(it!=W[d].end()) for(K k:it->second) work.push_back(k); } }
int main(int argc,char**argv){
  const char*m=argv[1]; const char*mask=argv[2]; NL=atoi(argv[3]); NR=atoi(argv[4]); u64 T=(u64)atof(argv[5]); size_t MAXC=argc>6?(size_t)atof(argv[6]):20000000; if(argc>7){ bst=argv[7][0]-'A'; bh=argv[7][1]-'0'; bside=argv[7][2]=='R'; bn=argv[7][3]-'0'; } // e.g. D0R0: state D reading 0 with a 0 on its right also counts as halting
  for(int i=0;i<6;i++)for(int b=0;b<2;b++){const char*t=m+i*7+b*3;int k=i*2+b; bad[k]=(t[0]=='-')||mask[k]=='*';
    if(t[0]=='-'){ns[k]=-1;w[k]=0;mv[k]=0;} else {w[k]=t[0]-'0';mv[k]=t[1]=='R'?1:-1;ns[k]=t[2]-'A';}}
  size_t TL=1u<<28; uint8_t*tape=(uint8_t*)calloc(TL,1); long pos=TL/2,lo=pos,hi=pos; int s=0;
  for(u64 t=0;t<T;t++){int k=s*2+tape[pos]; if(ns[k]<0){printf("HALTED during prefix\n");return 0;} tape[pos]=w[k];pos+=mv[k];s=ns[k]; if(pos<lo)lo=pos; if(pos>hi)hi=pos;}
  u64 ML=(1ULL<<NL)-1, MR=(1ULL<<NR)-1;
  // grams of the start tape at depth>=1 on both sides (plus blank)
  auto winL=[&](long p){u64 g=0; for(int i=0;i<NL;i++) g|=(u64)tape[p-1-i]<<i; return g;};  // cells p-1..p-NL
  auto winR=[&](long p){u64 g=0; for(int i=0;i<NR;i++) g|=(u64)tape[p+1+i]<<i; return g;};
  for(long p=pos-1;p>=lo-NL-2;p--) addG(0,winL(p));
  for(long p=pos+1;p<=hi+NR+2;p++) addG(1,winR(p));
  addG(0,0); addG(1,0);
  work.clear();
  addC(mk(s,tape[pos],winL(pos),winR(pos)));
  size_t done=0;
  while(!work.empty()){
    K k=work.back(); work.pop_back(); done++;
    int sh=k.b&15; int st=sh>>1,h=sh&1; u64 l=k.a,r=k.b>>4; int t=st*2+h;
    if(bst>=0 && st==bst && h==bh && ((bside? r : l)&1)==(u64)bn){ printf("HALTREACH configs=%zu pattern\n",C.size()); return 0; }
    if(bad[t]){ printf("HALTREACH configs=%zu slot=%c%d\n",C.size(),'A'+st,h); return 0; }
    if(mv[t]>0){ // move right: left gets w; old left window recorded; right shifts
      addG(0,l); u64 nl=((l<<1)|w[t])&ML; int nh=r&1; u64 pre=r>>1; // new right nearest n-1 cells = pre, far cell from grams
      auto &wl=W[1][pre]; wl.push_back(k); auto it=P[1].find(pre); int msk=it==P[1].end()?0:it->second;
      for(int x=0;x<2;x++) if(msk>>x&1) addC(mk(ns[t],nh,nl,pre|((u64)x<<(NR-1))));
    } else {
      addG(1,r); u64 nr=((r<<1)|w[t])&MR; int nh=l&1; u64 pre=l>>1;
      auto &wl=W[0][pre]; wl.push_back(k); auto it=P[0].find(pre); int msk=it==P[0].end()?0:it->second;
      for(int x=0;x<2;x++) if(msk>>x&1) addC(mk(ns[t],nh,pre|((u64)x<<(NL-1)),nr));
    }
    if(C.size()>MAXC){ printf("LIMIT configs=%zu\n",C.size()); return 0; }
  }
  printf("NONHALT configs=%zu lgrams=%zu rgrams=%zu\n",C.size(),G[0].size(),G[1].size());
}
