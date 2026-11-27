// calltest: is a trip's return state fixed by a few cells at its start, at EVERY boundary of the tape?
// A rightward trip at boundary b starts when the head steps from cell b to b+1 and ends when it steps back to b.
// The cells at and left of b cannot change or be read meanwhile, so the state on return is a function of the state
// at the start and of the tape right of b. The "call returns a known value" property of recursive-sweep proofs
// says that this function only looks at a bounded prefix. For every deep trip (depth > DEEP) the program records
//   key_K = (start state, first K cells beyond the boundary)  ->  set of return states
// and reports, for each K, how many deep trips have a key with more than one return state.
// Leftward trips are treated the same way (mirror image).
// Usage: calltest MACHINE STEPS [DEEP=256]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define T (1L<<27)
#define HB 24
#define NK 7
static const int KS[NK]={0,2,4,8,16,32,64};
static unsigned char *tape; static uint64_t *bits;
typedef struct { uint64_t k; uint32_t cnt; uint8_t mask; uint8_t id; } ent;
static ent *tab; static long ntab=0; static int full=0;
static inline uint64_t mix(uint64_t x){ x^=x>>33; x*=0xff51afd7ed558ccdULL; x^=x>>33; x*=0xc4ceb9fe1a85ec53ULL; x^=x>>33; return x; }
static ent* get(uint64_t k){ k=mix(k)|1; uint64_t i=k&((1L<<HB)-1);
  while(tab[i].k){ if(tab[i].k==k) return &tab[i]; i=(i+1)&((1L<<HB)-1);} if(ntab>(1L<<HB)*3/4){full=1; return NULL;} tab[i].k=k; ntab++; return &tab[i]; }
// 64 cells starting at q going right (bit j = cell q+j)
static inline uint64_t ctxR(long q){ long w=q>>6; int o=q&63; return o? (bits[w]>>o)|(bits[w+1]<<(64-o)) : bits[w]; }
// 64 cells starting at q going left (bit j = cell q-j)
static inline uint64_t rev64(uint64_t x){ x=((x>>1)&0x5555555555555555ULL)|((x&0x5555555555555555ULL)<<1); x=((x>>2)&0x3333333333333333ULL)|((x&0x3333333333333333ULL)<<2); x=((x>>4)&0x0f0f0f0f0f0f0f0fULL)|((x&0x0f0f0f0f0f0f0f0fULL)<<4); return __builtin_bswap64(x); }
static inline uint64_t ctxL(long q){ return rev64(ctxR(q-63)); }
typedef struct { uint64_t ctx; long far; long t0; uint8_t s; } fr;
int main(int argc,char**argv){
  char *m=argv[1]; long N=atol(argv[2]); int DEEP= argc>3? atoi(argv[3]):256;
  tape=calloc(T,1); bits=calloc(T/64+2,8); tab=calloc(1L<<HB,sizeof(ent));
  int w[6][2],d[6][2],n[6][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*x=m+7*s+3*b; if(x[0]=='-'){n[s][b]=-1;continue;} w[s][b]=x[0]-'0'; d[s][b]=x[1]=='R'?1:-1; n[s][b]=x[2]-'A';}
  long p=T/2; int s=0; long lo=p, hi=p;
  fr *st[2]; long sp[2]={0,0}; for(int k=0;k<2;k++) st[k]=malloc(sizeof(fr)*(1L<<24));
  long ndeep[2]={0,0}; double sdur[2]={0,0}, sdep[2]={0,0}; int retmask[2]={0,0}; long halt=-1;
  for(long i=0;i<N;i++){
    int b=tape[p]; if(n[s][b]<0){halt=i;break;}
    int wv=w[s][b], dv=d[s][b];
    if(wv!=b){ tape[p]=wv; bits[p>>6]^=1ULL<<(p&63); }
    p+=dv; s=n[s][b];
    if(p<lo)lo=p; if(p>hi)hi=p;
    if(p<1000||p>T-1000) { fprintf(stderr,"tape overflow\n"); break; }
    int dir= dv>0?0:1; // 0: moved right
    // push a trip in direction dir, pop a trip in the other direction
    { fr*f=&st[dir][sp[dir]++]; f->s=s; f->far=p; f->t0=i; f->ctx= dir==0? ctxR(p) : ctxL(p); }
    int o=1-dir;
    if(sp[o]>0){ fr*f=&st[o][--sp[o]];
      long depth = o==0? f->far-(p) : p-f->far;   // furthest cell reached beyond the boundary, in cells
      if(sp[o]>0){ fr*g=&st[o][sp[o]-1]; if(o==0? f->far>g->far : f->far<g->far) g->far=f->far; }
      if(depth>DEEP && i>N/100 && !full){ ndeep[o]++; sdur[o]+=i-f->t0; sdep[o]+=depth; retmask[o]|=1<<s;
        for(int j=0;j<NK;j++){ uint64_t c= KS[j]==64? f->ctx : (f->ctx & ((1ULL<<KS[j])-1));
          ent*e=get(mix(c)*0x9e3779b97f4a7c15ULL + f->s*131 + j*17 + o*7919 + 1); if(!e) break; e->cnt++; e->mask|=1<<s; e->id=(uint8_t)(1+o*NK+j); } }
    }
  }
  if(halt>=0){ printf("%s HALT %ld\n",m,halt); return 0; }
  static long amb[2][NK], tot[2][NK], kamb[2][NK], ktot[2][NK];
  for(long i=0;i<(1L<<HB);i++) if(tab[i].k){ ent*e=&tab[i]; int id=e->id-1; int o=id/NK, j=id%NK; tot[o][j]+=e->cnt; ktot[o][j]++; if(__builtin_popcount(e->mask)>1){ amb[o][j]+=e->cnt; kamb[o][j]++; } }
  printf("%s steps=%ld tape=%ld%s\n",m,N,hi-lo,full?" TABLEFULL":"");
  for(int o=0;o<2;o++){
    printf(" %s trips: deep=%ld dur/depth=%.1f ret=",o==0?"rightward":"leftward ",ndeep[o],sdep[o]>0?sdur[o]/sdep[o]:0.0);
    for(int z=0;z<6;z++) if(retmask[o]>>z&1) printf("%c",'A'+z);
    printf(" ambiguous:");
    for(int j=0;j<NK;j++) printf(" K%d=%.4f(%ld/%ld keys)",KS[j],tot[o][j]?(double)amb[o][j]/tot[o][j]:0.0,kamb[o][j],ktot[o][j]);
    printf("\n");
  }
  return 0;
}
