// wotest: direct test of the "write-only bulk / known return" property at one end of the tape.
// The machine is mirrored if needed so that the tested end is the LEFT end. E = leftmost 1.
// For each window width W: a trip starts when the head steps from E+W to E+W+1 and ends when it steps back to E+W.
// During a trip the window cells E..E+W cannot change. Recorded per trip:
//   key  = (state at exit, cells E..E+W)             prefix_K = cells E+W+1..E+W+K at exit
//   depth = furthest distance beyond the window        ret = state on re-entry
// Questions answered:
//   1. how many distinct keys, by quarter of the run (finite controller?)
//   2. is ret a function of (key, prefix_K), for K = 0,1,2,4,8,16,32, on deep trips (depth > 32)?
//   3. is the next key a function of (key, ret)?  (it is unless the end retreats and bulk cells enter the window)
//   4. where does the halting state occur (distance from E)?
// Usage: wotest MACHINE L|R STEPS [DEEP=32]   (a trip is "deep" if it goes more than DEEP cells beyond the window)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define T (1L<<28)
#define HB 23
#define NW 6
#define NK 8
static const int WS[NW]={4,8,16,24,32,48};
static const int KS[NK]={0,1,2,4,8,16,32,64};
static unsigned char *tape;
typedef struct { uint64_t k; uint32_t cnt; uint8_t mask; uint8_t fl; uint64_t aux; } ent;
static ent *tab; static long ntab=0;
static inline uint64_t mix(uint64_t x){ x^=x>>33; x*=0xff51afd7ed558ccdULL; x^=x>>33; x*=0xc4ceb9fe1a85ec53ULL; x^=x>>33; return x; }
static ent* get(uint64_t k){ k=mix(k)|1; uint64_t i=k&((1L<<HB)-1);
  while(tab[i].k){ if(tab[i].k==k) return &tab[i]; i=(i+1)&((1L<<HB)-1);} if(ntab>(1L<<HB)*3/4){fprintf(stderr,"table full\n");exit(1);} tab[i].k=k; ntab++; return &tab[i]; }
int main(int argc,char**argv){
  char *m=argv[1]; int mirror = argv[2][0]=='R'; long N=atol(argv[3]); int DEEP= argc>4? atoi(argv[4]):32;
  tape=calloc(T,1); tab=calloc(1L<<HB,sizeof(ent));
  int w[6][2],d[6][2],n[6][2]; int hs=-1,hb=-1;
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*x=m+7*s+3*b; if(x[0]=='-'){n[s][b]=-1;hs=s;hb=b;continue;} w[s][b]=x[0]-'0'; d[s][b]=x[1]=='R'?1:-1; if(mirror)d[s][b]=-d[s][b]; n[s][b]=x[2]-'A';}
  long p=T/2, lo1=T, hi1=-1; int s=0;
  // per W
  int intrip[NW]={0}; long tripmax[NW]; uint64_t key[NW]; uint64_t pk[NW][NK]; long base[NW];
  long ntrip[NW]={0}, ndeep[NW]={0}; long nkeys[NW]={0}, qkeys[NW][4]; long ndkeys[NW]={0}, qdkeys[NW][4];
  uint64_t prevkr[NW]={0}; int retmask[NW]={0};
  long retreat=0; double sdur[NW]={0}, sdep[NW]={0}; long t0[NW]={0}; long hcount=0, hmin=1L<<60, hmax=-1; long hhist[8]={0};
  long halt=-1; long maxlen=0;
  for(long i=0;i<N;i++){
    int b=tape[p]; if(n[s][b]<0){halt=i;break;}
    int wv=w[s][b], dv=d[s][b];
    tape[p]=wv;
    if(wv){ if(p<lo1)lo1=p; if(p>hi1)hi1=p; }
    else if(b){ if(lo1==hi1 && p==lo1){lo1=T;hi1=-1;} else { if(p==lo1){ while(!tape[lo1]) lo1++; if(i>N/100) retreat++; } if(p==hi1){ while(!tape[hi1]) hi1--; } } }
    long op=p; p+=dv; s=n[s][b];
    if(p<1000||p>T-1000) { fprintf(stderr,"tape overflow\n"); break; }
    if(hi1<0 || i<=N/100) { for(int a=0;a<NW;a++) intrip[a]=0; goto q; }
    if(s==hs){ long dist=p-lo1; hcount++; if(dist<hmin)hmin=dist; if(dist>hmax)hmax=dist; int bk= dist<0?0: dist<=8?1: dist<=24?2: dist<=48?3: dist<=100?4: dist<=1000?5: dist<=100000?6:7; hhist[bk]++; }
    for(int a=0;a<NW;a++){
      int W=WS[a];
      if(!intrip[a]){
        if(dv>0 && op==lo1+W){ // exit
          intrip[a]=1; base[a]=lo1; tripmax[a]=p; t0[a]=i;
          uint64_t k=(uint64_t)(a*8+s+1); for(long q=lo1;q<=lo1+W;q++) k=k*1000003+tape[q]+1; k=mix(k); key[a]=k;
          ent*e=get(k*31+7); if(!e->cnt){ nkeys[a]++; } e->cnt++;
          // prefix keys
          uint64_t h=k; int kk=0; for(int j=0;j<NK;j++){ for(;kk<KS[j];kk++) h=h*1000003+tape[lo1+W+1+kk]+1; pk[a][j]=mix(h*131+j); }
          // next-key determinism
          if(prevkr[a]){ ent*t=get(prevkr[a]); if(!t->cnt){ t->cnt=1; t->aux=k; t->mask=a; } else if(t->aux!=k) t->fl=1; }
        }
      } else {
        if(p>tripmax[a]) tripmax[a]=p;
        if(dv<0 && p==base[a]+W){ // return
          intrip[a]=0; ntrip[a]++; long depth=tripmax[a]-(base[a]+W);
          prevkr[a]=mix(key[a]*37+s+11)|1;
          if(depth>DEEP){ ndeep[a]++; sdur[a]+=i-t0[a]; sdep[a]+=depth; retmask[a]|=1<<s;
            ent*e=get(key[a]*31+9); if(!e->cnt) ndkeys[a]++; e->cnt++;
            for(int j=0;j<NK;j++){ ent*e=get(pk[a][j]); e->cnt++; e->mask|=1<<s; e->fl=(uint8_t)(100+a*NK+j); } }
        }
      }
    }
    q:
    if(hi1-lo1>maxlen) maxlen=hi1-lo1;
    for(int k=1;k<=4;k++) if(i+1==N/4*k) for(int a=0;a<NW;a++){ qkeys[a][k-1]=nkeys[a]; qdkeys[a][k-1]=ndkeys[a]; }
  }
  if(halt>=0){ printf("%s HALT %ld\n",m,halt); return 0; }
  // tally
  static long amb[NW][NK], tot[NW][NK], kamb[NW][NK], ktot[NW][NK]; long nkconf[NW]={0}, nktot[NW]={0};
  for(long i=0;i<(1L<<HB);i++) if(tab[i].k){ ent*e=&tab[i];
    if(e->fl<100 && e->aux){ nktot[e->mask]++; if(e->fl) nkconf[e->mask]++; }
    if(e->fl>=100){ int id=e->fl-100; int a=id/NK, j=id%NK; tot[a][j]+=e->cnt; ktot[a][j]++; if(__builtin_popcount(e->mask)>1){ amb[a][j]+=e->cnt; kamb[a][j]++; } }
  }
  printf("%s end=%c steps=%ld tape=%ld retreats=%ld halting_state=%c reads %d: visits=%ld dist[min,max]=[%ld,%ld] hist(<0,<=8,<=24,<=48,<=100,<=1e3,<=1e5,more)=",m,argv[2][0],N,maxlen,retreat,'A'+hs,hb,hcount,hmin,hmax);
  for(int k=0;k<8;k++) printf("%ld%s",hhist[k],k<7?",":"\n");
  for(int a=0;a<NW;a++){
    printf(" W=%2d trips=%ld deep=%ld keys=%ld,%ld,%ld,%ld deepkeys=%ld,%ld,%ld,%ld retstates=",WS[a],ntrip[a],ndeep[a],qkeys[a][0],qkeys[a][1],qkeys[a][2],qkeys[a][3],qdkeys[a][0],qdkeys[a][1],qdkeys[a][2],qdkeys[a][3]);
    for(int z=0;z<6;z++) if(retmask[a]>>z&1) printf("%c",'A'+z);
    printf(" nextkey_conflicts=%ld/%ld durperdepth=%.1f",nkconf[a],nktot[a],sdep[a]>0?sdur[a]/sdep[a]:0.0); printf(" ambiguous deep trips by K:");
    for(int j=0;j<NK;j++) printf(" K%d=%ld/%ld(%ld/%ld keys)",KS[j],amb[a][j],tot[a][j],kamb[a][j],ktot[a][j]);
    printf("\n");
  }
  return 0;
}
