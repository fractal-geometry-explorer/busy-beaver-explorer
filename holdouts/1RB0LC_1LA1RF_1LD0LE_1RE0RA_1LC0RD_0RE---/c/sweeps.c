// sweeps: direct simulation; prints the turning points of the head (moves of at least T cells between them).
// During a rebuild the "min" points are the positions of the reflector Q.  usage: ./sweeps MACHINE FROM TO T
// sweeps M from to T : print turning points of the head trajectory with hysteresis T (step state pos kind)
#include <stdio.h>
#include <stdlib.h>
int W[6][2],Mv[6][2],N[6][2];
int main(int c,char**v){
  char*m=v[1]; long long from=atoll(v[2]), to=atoll(v[3]); long long T=atoll(v[4]);
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*p=m+s*7+r*3; if(p[2]=='-'){N[s][r]=-1;continue;} W[s][r]=p[0]-'0';Mv[s][r]=p[1]=='R'?1:-1;N[s][r]=p[2]-'A';}
  long long S=1<<28; unsigned char*t=calloc(S,1); long long h=S/2,lo=h,hi=h; int st=0;
  int trend=1; long long ext=h, extk=0; int extst=0;
  for(long long k=1;k<=to;k++){
    int r=t[h]; int ns=N[st][r]; if(ns<0){printf("HALT %lld\n",k);return 0;}
    t[h]=W[st][r]; h+=Mv[st][r]; st=ns;
    if(h<lo)lo=h; if(h>hi)hi=h;
    if(trend==1){ if(h>ext){ext=h;extk=k;extst=st;} else if(ext-h>=T){ if(extk>=from) printf("%lld %c %lld max lo=%lld hi=%lld\n",extk,'A'+extst,ext-S/2,lo-S/2,hi-S/2); trend=-1; ext=h;extk=k;extst=st;} }
    else { if(h<ext){ext=h;extk=k;extst=st;} else if(h-ext>=T){ if(extk>=from) printf("%lld %c %lld min lo=%lld hi=%lld\n",extk,'A'+extst,ext-S/2,lo-S/2,hi-S/2); trend=1; ext=h;extk=k;extst=st;} }
  }
  return 0;}
