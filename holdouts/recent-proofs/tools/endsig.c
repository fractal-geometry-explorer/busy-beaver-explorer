// endsig: two end signatures read off a plain run.
//  B ("run grammar"): when the head, moving outward, stands at or beyond the last 1 on side S (nothing but blank
//     behind it), cut the whole tape into maximal runs and collect the distinct trigrams of run lengths.
//  (the sequence of these words is also tested for eventual periodicity)
//  A ("end controller"): when the head comes back within W cells of the last 1 on side S after being more than 2W
//     away, record (state, cells between that end and the head).
// Prints, per side, the number of samples and the number of distinct items after each quarter of the run.
// Usage: endsig MACHINE STEPS [W=24]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define T (1L<<27)
#define HB 21
#define SEQ (1L<<22)
static unsigned char *tape;
typedef struct { uint64_t *t; long n; } set;
static void sinit(set*s){ s->t=calloc(1L<<HB,8); s->n=0; }
static inline uint64_t mix(uint64_t x){ x^=x>>33; x*=0xff51afd7ed558ccdULL; x^=x>>33; x*=0xc4ceb9fe1a85ec53ULL; x^=x>>33; return x|1; }
static void sadd(set*s,uint64_t k){ if(s->n>(1L<<HB)*3/4) return; k=mix(k); uint64_t i=k&((1L<<HB)-1);
  while(s->t[i]){ if(s->t[i]==k) return; i=(i+1)&((1L<<HB)-1);} s->t[i]=k; s->n++; }
int main(int argc,char**argv){
  char *m=argv[1]; long N=atol(argv[2]); int W= argc>3? atoi(argv[3]):24;
  tape=calloc(T,1);
  int w[6][2],d[6][2],n[6][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*x=m+7*s+3*b; if(x[0]=='-'){n[s][b]=-1;continue;} w[s][b]=x[0]-'0'; d[s][b]=x[1]=='R'?1:-1; n[s][b]=x[2]-'A';}
  long p=T/2, lo1=T, hi1=-1; int s=0;
  set B[2],A[2]; for(int k=0;k<2;k++){sinit(&B[k]);sinit(&A[k]);}
  long nB[2]={0,0}, nA[2]={0,0}, lastB[2]={0,0}; int away[2]={0,0}; int max1[2]={0,0}, max0[2]={0,0};
  long qB[2][4], qA[2][4]; long halt=-1;
  uint32_t *seq[2]; long ns[2]={0,0}; for(int k=0;k<2;k++) seq[k]=malloc(4L*SEQ);
  for(long i=0;i<N;i++){
    int b=tape[p]; if(n[s][b]<0){halt=i;break;}
    int wv=w[s][b], dv=d[s][b];
    tape[p]=wv;
    if(wv){ if(p<lo1)lo1=p; if(p>hi1)hi1=p; }
    else if(b){ if(lo1==hi1 && p==lo1){lo1=T;hi1=-1;} else { if(p==lo1){ while(!tape[lo1]) lo1++; } if(p==hi1){ while(!tape[hi1]) hi1--; } } }
    p+=dv; s=n[s][b];
    if(p<1000||p>T-1000) { fprintf(stderr,"tape overflow\n"); break; }
    if(hi1>=0){
      for(int side=0;side<2;side++){
        long dist = side==0? p-lo1 : hi1-p; int out = side==0? dv<0 : dv>0;
        if(dist>2*W) away[side]=1;
        if(out && dist<=W && away[side] && i>N/100){ away[side]=0; nA[side]++;
          uint64_t k=s+1; int step= side==0?1:-1; long q= side==0?lo1:hi1; int len=0;
          if(dist>=0) for(;len<=dist;len++,q+=step) k=k*3+tape[q]+1; else k=k*7+(uint64_t)(-dist);
          sadd(&A[side],k*4+side); if(ns[side]<SEQ) seq[side][ns[side]++]=(uint32_t)mix(k); }
        if(out && dist<=0 && i-lastB[side]>=hi1-lo1+1 && i>N/100){ lastB[side]=i; nB[side]++;
          int step= side==0?1:-1; long q= side==0?lo1:hi1; long end= side==0?hi1:lo1;
          uint64_t r0=0,r1=0; int idx=0;
          while(side==0? q<=end : q>=end){ int v=tape[q]; long c=0; while((side==0? q<=end : q>=end) && tape[q]==v){c++; q+=step;}
            if(v){ if(c>max1[side]) max1[side]=c>1000000?1000000:c; } else { if(c>max0[side]) max0[side]=c>1000000?1000000:c; }
            uint64_t cc=c>4000?4000:c;
            if(idx>=2) sadd(&B[side], ((((uint64_t)(s*2+v)*4001+r0)*4001+r1)*4001+cc));
            r0=r1; r1=cc; idx++; }
        }
      }
    }
    for(int k=1;k<=4;k++) if(i+1==N/4*k) for(int side=0;side<2;side++){ qB[side][k-1]=B[side].n; qA[side][k-1]=A[side].n; }
  }
  if(halt>=0){ printf("%s HALT %ld\n",m,halt); return 0; }
  printf("%s",m);
  for(int side=0;side<2;side++) printf(" | %c B n=%ld max1=%d max0=%d tri=%ld,%ld,%ld,%ld A n=%ld words=%ld,%ld,%ld,%ld", side?'R':'L', nB[side],max1[side],max0[side],qB[side][0],qB[side][1],qB[side][2],qB[side][3], nA[side],qA[side][0],qA[side][1],qA[side][2],qA[side][3]);
  // smallest period of the sequence of end words over its second half (0 = none up to 50000)
  for(int side=0;side<2;side++){ long nn=ns[side], per=0; if(nn>=40){ for(long pp=1; pp<=50000 && pp<=nn/4; pp++){ int ok=1; for(long i=nn/2;i<nn;i++) if(seq[side][i]!=seq[side][i-pp]){ok=0;break;} if(ok){per=pp;break;} } }
    printf(" | %c period=%ld", side?'R':'L', per); }
  printf("\n"); return 0;
}
