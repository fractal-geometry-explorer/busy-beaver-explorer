#include <stdio.h>
#include <stdlib.h>
// L-turn positions (hysteresis H): print every EV-th, and every jump left by more than J
int main(int c,char**v){
  char*m=v[1]; long long N=atoll(v[2]); long H=atol(v[3]); long EV=atol(v[4]); long J=atol(v[5]);
  int W[6][2],D[6][2],S[6][2];
  for(int s=0;s<6;s++)for(int y=0;y<2;y++){char*g=m+7*s+3*y; if(g[2]=='-'){S[s][y]=-1;continue;} W[s][y]=g[0]-'0';D[s][y]=g[1]=='R'?1:-1;S[s][y]=g[2]-'A';}
  long SZ=1L<<27; unsigned char*t=calloc(SZ,1); long O=SZ/2,p=O,lo=O,hi=O; int q=0; int mode=-1; long ext=O; long long et=0; long long k=0; long prevL=O;
  for(long long i=0;i<N;i++){
    int y=t[p]; int ns=S[q][y]; if(ns<0){printf("HALT %lld\n",i+1);return 0;}
    t[p]=W[q][y]; p+=D[q][y]; q=ns; if(p<lo)lo=p; if(p>hi)hi=p;
    if((mode==-1&&p>ext+H)||(mode==1&&p<ext-H)){
      if(mode==-1){ k++; if(k%EV==0 || ext<prevL-J) printf("%lld %lld L=%ld lo=%ld hi=%ld%s\n",k,et,ext-O,lo-O,hi-O, ext<prevL-J?" JUMP":""); prevL=ext;}
      mode=-mode; ext=p;
    } else if((mode==-1&&p<ext)||(mode==1&&p>ext)){ext=p;et=i+1;}
  }
  printf("end k=%lld lo=%ld hi=%ld\n",k,lo-O,hi-O); return 0;
}
