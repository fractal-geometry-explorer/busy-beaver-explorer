// lapcs: lap-level crossing-sequence screen for a 2-symbol Turing machine.
// Usage: lapcs MACHINE NSTEPS SIDE(L|R) [DUMP]
// A lap starts each time the head stands on the outermost visited cell of the home side and steps away from it.
// For every cell boundary we record the crossing sequence of the lap (state after the step, direction), interned in a trie.
// A row letter is (cell before the lap, head mark, crossing sequence on the far side of the cell).
// Output at checkpoints: laps, distinct crossing sequences, longest one, distinct k-grams of row letters (k=1..4),
// and how often the next crossing sequence is predicted by the previous one plus r cells of look-ahead,
// in both directions (out = away from home, in = toward home).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint64_t u64; typedef uint32_t u32; typedef uint8_t u8;
#define W (1<<23)
#define TRCAP (1<<22)
#define TRTAB (1<<23)
#define GTAB (1<<23)
#define DTAB (1<<22)
static u8 tape[W], oldv[W]; static u32 wst[W], cst[W], csn[W];
static u64 trk[TRTAB]; static u32 trv[TRTAB]; static u32 par[TRCAP]; static u8 pval[TRCAP]; static u32 dep[TRCAP]; static u8 fin[TRCAP];
static u32 ntr=1, nfin=0, maxlen=0;
static u64 gset[GTAB]; static u64 gcnt[6]; static int gfull=0;
static u64 dk[DTAB]; static u32 dv[DTAB]; 
#define ND 8
static u64 dkeys[ND], dconf[ND], docc[ND], dmis[ND];
static inline u64 mix(u64 x){x^=x>>33;x*=0xff51afd7ed558ccdULL;x^=x>>33;x*=0xc4ceb9fe1a85ec53ULL;x^=x>>33;return x;}
static int trfull=0;
static inline u32 child(u32 n,u32 v){
  u64 key=(u64)n*16+v+1; u64 h=mix(key)&(TRTAB-1);
  while(trk[h]){ if(trk[h]==key) return trv[h]; h=(h+1)&(TRTAB-1);}
  if(ntr>=TRCAP){trfull=1;return 0;}
  trk[h]=key; trv[h]=ntr; par[ntr]=n; pval[ntr]=v; dep[ntr]=dep[n]+1; return ntr++;
}
static inline void gadd(int k,u64 h){
  h=mix(h+k*0x9e3779b97f4a7c15ULL)|1; u64 i=h&(GTAB-1);
  while(gset[i]){ if(gset[i]==h) return; i=(i+1)&(GTAB-1);}
  if(gcnt[0]>GTAB*3/4){gfull=1;return;}
  gset[i]=h; gcnt[0]++; gcnt[k]++;
}
static inline void dadd(int d,u64 key,u32 val){
  key=mix(key+d*0x9e3779b97f4a7c15ULL)|1; u64 i=key&(DTAB-1); docc[d]++;
  while(dk[i]){ if(dk[i]==key){ u32 v=dv[i]; if((v&0x7fffffff)!=val){ dmis[d]++; if(!(v>>31)){dv[i]|=0x80000000u; dconf[d]++;} } return;} i=(i+1)&(DTAB-1);}
  if(dkeys[0]+dkeys[1]+dkeys[2]+dkeys[3]+dkeys[4]+dkeys[5]+dkeys[6]+dkeys[7]>DTAB*3/4) return;
  dk[i]=key; dv[i]=val; dkeys[d]++;
}
int T[6][2][3];
int main(int argc,char**argv){
  if(argc<4){fprintf(stderr,"usage\n");return 1;}
  const char*m=argv[1]; u64 N=strtoull(argv[2],0,10); int mir=(argv[3][0]=='R'); int dump=argc>4?atoi(argv[4]):0; int full=argc>5?atoi(argv[5]):0; long maxp=W/2, far=W/2; int reached=1;
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*t=m+s*7+b*3; if(t[0]=='-'){T[s][b][2]=-1;continue;}
    T[s][b][0]=t[0]-'0'; int d=(t[1]=='R')?1:-1; if(mir)d=-d; T[s][b][1]=d; T[s][b][2]=t[2]-'A';}
  long p=W/2, minp=W/2; int s=0; u32 lap=1; long lo=p,hi=p; long startp=p; int starts=0; int started=0;
  u64 laps=0, t=0, next=N/16; u64 lastlapt=0, maxlapt=0; int halted=0;
  static u64 L[1<<22]; // letters of a row (bounded scan width)
  for(;;){
    int b=tape[p]; int*tr=T[s][b];
    if(tr[2]<0){halted=1;break;}
    if(p==minp && tr[1]==1 && (!full||reached||!started)){
      // lap boundary: finish previous lap
      if(started){
        long a=lo-5, z=hi+5; if(a<1)a=1; if(z>=W-1)z=W-2;
        long n=z-a+1;
        if(n<(1<<22)){
          // mark final crossing sequences
          for(long i=a-1;i<=z;i++){ u32 c=(cst[i]==lap)?csn[i]:0; if(c&&!fin[c]){fin[c]=1;nfin++; if(dep[c]>maxlen)maxlen=dep[c];} }
          for(long i=a;i<=z;i++){
            u32 c=(cst[i]==lap)?csn[i]:0; int w=(wst[i]==lap)?oldv[i]:tape[i]; int mk=(i==startp)?starts+1:0;
            L[i-a]=mix(((u64)c<<8)|(w<<4)|mk);
          }
          for(long i=0;i<n;i++){ u64 h=L[i]; gadd(1,h); for(int k=2;k<=4&&i+k<=n;k++){h=mix(h*31+L[i+k-1]);gadd(k,h);} }
          // determinism: only cells with a nonempty crossing on at least one side
          for(long i=a+1;i<z;i++){
            u32 cl=(cst[i-1]==lap)?csn[i-1]:0, cr=(cst[i]==lap)?csn[i]:0; if(!cl&&!cr) continue;
            #define WB(j) (((j)<1||(j)>=W-1)?0:((wst[j]==lap)?oldv[j]:tape[j]))
            int mk=(i==startp)?starts+1:0;
            u64 ko=((u64)cl<<8)|(WB(i)<<4)|mk, ki=((u64)cr<<8)|(WB(i)<<4)|mk;
            u64 fo=0,fi=0; int r=0; static const int R[4]={0,2,6,16};
            for(int q=0;q<4;q++){ for(;r<R[q];r++){ fo=fo*2+WB(i+1+r)+1; fi=fi*2+WB(i-1-r)+1; }
              dadd(q,mix(ko)+fo*0x9e3779b1u,cr); dadd(4+q,mix(ki)+fi*0x9e3779b1u,cl); }
          }
          if(dump&&laps<(u64)dump){ printf("LAP %llu start %c at %ld range %ld..%ld:",(unsigned long long)laps,'A'+starts,startp-minp,lo-minp,hi-minp);
            for(long i=lo;i<=hi&&i<lo+200;i++){u32 c=(cst[i]==lap)?csn[i]:0; printf(" %d/%u",(wst[i]==lap)?oldv[i]:tape[i],dep[c]);} printf("\n"); }
        }
        laps++; if(t-lastlapt>maxlapt)maxlapt=t-lastlapt; lastlapt=t;
        if(t>=next){
          printf("CK t=%llu laps=%llu cs=%u maxlen=%u trie=%u g1=%llu g2=%llu g3=%llu g4=%llu",(unsigned long long)t,(unsigned long long)laps,nfin,maxlen,ntr,
            (unsigned long long)gcnt[1],(unsigned long long)gcnt[2],(unsigned long long)gcnt[3],(unsigned long long)gcnt[4]);
          for(int d=0;d<ND;d++) printf(" %s%d=%llu/%llu/%llu/%llu",d<4?"o":"i",d&3,(unsigned long long)dkeys[d],(unsigned long long)dconf[d],(unsigned long long)dmis[d],(unsigned long long)docc[d]);
          printf(" width=%ld maxlap=%llu%s\n",hi-minp,(unsigned long long)maxlapt,gfull?" GFULL":"");
          while(next<=t) next*=2; if(t>=N) break;
        }
        lap++; 
      }
      started=1; startp=p; starts=s; lo=hi=p; far=maxp; reached=(far==p);
    }
    if(t>=N+N/2) break;
    if(started && wst[p]!=lap){wst[p]=lap; oldv[p]=b;}
    tape[p]=tr[0]; long q=p+tr[1]; s=tr[2];
    if(started){ long bd=tr[1]==1?p:q; u32 cur=(cst[bd]==lap)?csn[bd]:0; cur=child(cur,(u32)s*2+(tr[1]==1)); if(trfull)break; cst[bd]=lap; csn[bd]=cur; }
    p=q; if(p>maxp)maxp=p; if(p>=far)reached=1; if(p<minp)minp=p; if(p<lo)lo=p; if(p>hi)hi=p; t++;
    if(p<8||p>W-8){printf("TAPEFULL\n");break;}
  }
  printf("END t=%llu laps=%llu halted=%d triefull=%d cs=%u maxlen=%u\n",(unsigned long long)t,(unsigned long long)laps,halted,trfull,nfin,maxlen);
  return 0;
}
