// DeepMind map of 1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC--- (copied from holdouts/.../lean/DeepMindMap.lean), accelerated chain rule
#include <stdio.h>
#include <stdlib.h>
typedef unsigned long long u;
int main(int c,char**v){ double N=atof(v[1]); u m=0,k=0,b=2; u mx=0; u it=0; u NN=atoll(v[2]); u nc=0; int ch;
 for(u i=1;i<=(u)N;i++){
  ch=0;
  if(b==0){m=m+1;b=2*k+2;k=0;}
  else if(m==0&&b==1){m=2*k+3;k=0;b=2;}
  else if(m==0){m=2*k+2;k=1;b-=2;}
  else if(m==1&&k==0){m=0;b=b+2;}
  else if(m==1&&b==1){m=2*(k-1)+7;k=0;b=2;}
  else if(m==1){m=2*(k-1)+6;k=1;b-=2;}
  else if(m==2&&k==0&&b==1){m=0;k=1;b=0;}
  else if(m==2&&k==0){printf("HALT at map step %llu (raw %llu) b=%llu\n",i,it,b);return 0;}
  else if(m==2&&k==1){m=0;k=1;}
  else if(m==2&&b==1){m=2*(k-2)+7;k=0;b=2;}
  else if(m==2){m=2*(k-2)+6;k=1;b-=2;}
  else { u t=m/3; if(t>b)t=b; m-=3*t;k+=2*t;b-=t; it+=t-1; ch=1; }
  it++; if(m>mx)mx=m; if(k>mx)mx=k; if(b>mx)mx=b;
  if(mx>(1ULL<<61)){printf("OVERFLOW at %llu\n",i);return 1;}
  if(!ch){nc++; if(nc<=12||nc==NN) printf("(%llu,%llu,%llu) ",m,k,b);}
  if((i&(i-1))==0&&i>1000000) printf("\nstep %llu raw %llu (%llu,%llu,%llu) max %llu",i,it,m,k,b,mx);
 } printf("\ndone %.0f accelerated steps (raw %llu) no halt, max %llu\n",N,it,mx);}
