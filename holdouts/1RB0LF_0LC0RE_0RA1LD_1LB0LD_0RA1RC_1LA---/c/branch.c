// branch: the true run of 1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA--- (START A) or the twin (START D, mirrored).  At
// each reset record 0^inf 1 B> 1 0 (10)^X T with X >= 36, for each delta: copy the tape, replace X by X + delta, and
// run the copy unchanged for NB more resets or until it halts; then go on with the true run.
// usage: branch MAXRESET NB START d1 d2 ...
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int W[6][2]={{1,0},{0,0},{0,1},{1,0},{0,1},{1,0}};
static int Mv[6][2]={{1,-1},{-1,1},{1,-1},{-1,-1},{1,1},{-1,0}};
static int Nx[6][2]={{1,5},{2,4},{0,3},{1,3},{0,2},{0,-1}};
#define N (1L<<28)
typedef struct {unsigned char*t; long h,lo,hi; int s; unsigned long long st;} M;
// run until the next reset record (returns X, h at the record) or halt (returns -1)
long run_to_reset(M*m, long*kout){
  unsigned char*t=m->t; long h=m->h,lo=m->lo,hi=m->hi; int s=m->s; unsigned long long st=m->st; long res=-2;
  for(;;){
    if(h<=1||h>=N-2){res=-3;break;}
    int c=t[h];
    if(s==5&&c==1){res=-1;break;}
    if(s==1&&h<lo){
      lo=h;
      if(t[h]==1&&t[h-1]==1&&t[h+1]==0){
        long k=h+2,X=0; while(t[k]==1&&t[k+1]==0){X++;k+=2;}
        if(X>=36){res=X;*kout=k;break;}
      }
    }
    t[h]=W[s][c]; h+=Mv[s][c]; s=Nx[s][c]; st++; if(h>hi)hi=h;
  }
  m->h=h;m->lo=lo;m->hi=hi;m->s=s;m->st=st; return res;
}
void setX(M*m,long X,long k,long Xn){
  long d=2*(Xn-X); unsigned char*t=m->t;
  memmove(t+k+d,t+k,m->hi-k+2); if(d<0) memset(t+m->hi+d+2,0,-d);
  for(long j=0;j<Xn;j++){t[m->h+2+2*j]=1;t[m->h+3+2*j]=0;}
  m->hi+=d;
}
int main(int argc,char**argv){
  long MR=atol(argv[1]),NB=atol(argv[2]); int start=argv[3][0]-'A'; int nd=argc-4; long D[64]; for(int i=0;i<nd;i++)D[i]=atol(argv[4+i]);
  M m={calloc(N,1),N/16,N/16,N/16,start,0}; M b={calloc(N,1),0,0,0,0,0};
  for(long r=1;r<=MR;r++){
    long k; long X=run_to_reset(&m,&k);
    if(X<0){printf("TRUE RUN STOPPED %ld\n",X);return 0;}
    printf("reset %ld X=%ld step %llu width %ld:",r,X,m.st,m.hi-m.lo); fflush(stdout);
    for(int i=0;i<nd;i++){
      long lo0=m.lo-4; memcpy(b.t+lo0,m.t+lo0,m.hi-lo0+4);
      b.h=m.h;b.lo=m.lo;b.hi=m.hi;b.s=m.s;b.st=0;
      setX(&b,X,k,X+D[i]);
      // step off the record so run_to_reset does not stop here: run one step
      long res=0,kk;
      { int c=b.t[b.h]; b.t[b.h]=W[b.s][c]; b.h+=Mv[b.s][c]; b.s=Nx[b.s][c]; b.st++; }
      long j; for(j=0;j<NB;j++){res=run_to_reset(&b,&kk); if(res<0)break; int c=b.t[b.h]; b.t[b.h]=W[b.s][c]; b.h+=Mv[b.s][c]; b.s=Nx[b.s][c]; b.st++;}
      if(res==-1) printf(" %+ld:HALT(phase %ld)",D[i],j+1); else if(res<0) printf(" %+ld:?%ld",D[i],res); else printf(" %+ld:ok",D[i]);
      fflush(stdout);
      { long a=b.lo-8<lo0?b.lo-8:lo0; if(a<0)a=0; long e=b.hi+8; if(e>N)e=N; memset(b.t+a,0,e-a); }
    }
    printf("\n");
    { int c=m.t[m.h]; m.t[m.h]=W[m.s][c]; m.h+=Mv[m.s][c]; m.s=Nx[m.s][c]; m.st++; }
  }
  return 0;
}
