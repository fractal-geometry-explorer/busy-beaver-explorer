#include <stdio.h>
#include <stdlib.h>
#include <string.h>
// usage: snap MACHINE MAXSTEPS SIDE(L|R) EVERY [T0]
// prints at every EVERY-th turnaround on SIDE (head extreme in a sweep, hysteresis 6): t pos state lo hi bits(lo..hi)
int main(int c,char**v){
  char*m=v[1]; long long N=atoll(v[2]); char side=v[3][0]; long ev=atol(v[4]); long long T0=c>5?atoll(v[5]):0;
  int W[6][2],D[6][2],S[6][2];
  for(int s=0;s<6;s++)for(int y=0;y<2;y++){char*g=m+7*s+3*y; if(g[2]=='-'){S[s][y]=-1;continue;} W[s][y]=g[0]-'0';D[s][y]=g[1]=='R'?1:-1;S[s][y]=g[2]-'A';}
  long SZ=1L<<26; unsigned char*t=calloc(SZ,1); long O=SZ/2,p=O,lo=O,hi=O; int q=0; int mode=-1; long ext=O; long long ext_t=0; int ext_q=0; long k=0;
  for(long long i=0;i<N;i++){
    int y=t[p]; int ns=S[q][y]; if(ns<0){printf("HALT %lld\n",i+1);return 0;}
    t[p]=W[q][y]; p+=D[q][y]; q=ns; if(p<lo)lo=p; if(p>hi)hi=p;
    if((mode==-1&&p>ext+6)||(mode==1&&p<ext-6)){
      char sd=mode==-1?'L':'R';
      if(sd==side && i>=T0){ k++; if(k%ev==0){ printf("%lld %ld %c %ld %ld ",ext_t,ext-O,'A'+ext_q,lo-O,hi-O); for(long j=lo;j<=hi;j++)putchar('0'+t[j]); putchar('\n'); } }
      mode=-mode; ext=p;
    } else if((mode==-1&&p<ext)||(mode==1&&p>ext)){ext=p;ext_t=i+1;ext_q=q;}
  }
  return 0;
}
