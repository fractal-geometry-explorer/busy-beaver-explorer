#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef unsigned long long u;
int main(int c,char**v){ double N=atof(v[1]); u a=2,b=9; long double steps=52; u maxs=0; u near=0;
 for(u i=1;i<=(u)N;i++){
  if(b==3){printf("HALT at visit %llu a=%llu steps~%Le\n",i,a,steps);return 0;}
  if(a%2==0 && b>=a+3){ if(b==a+4) {printf("HALT next visit %llu a=%llu\n",i,a);} steps+=2.0L*a*a+12.0L*a-1; u na=2*a+4; b=b-a-1; a=na;}
  else if(a%2==1 && b>=a+4){steps+=2.0L*a*a+12.0L*a+13; u na=2*a+3; b=b-a; a=na;}
  else if(a%2==1 && b==a+3){steps+=2.0L*a*a+12.0L*a+39; a=2*a+1; b=9;}
  else if(b==a+2 && a>=2){steps+=2.0L*a*a+9.0L*a+23; b=2*a+7; a=1;}
  else if(b==a+1 && a>=3){steps+=2.0L*a*a+5.0L*a+7; b=2*a+4; a=4;}
  else if(a>=b && b>=4){steps+=2.0L*b*b+b+5; u na=a-b+1; b=2*b+3; a=na;}
  else if(b==2 && a>=4){steps+=25; a-=3; b=7;}
  else {printf("STUCK a=%llu b=%llu at %llu\n",a,b,i);return 1;}
  if(a>maxs)maxs=a; if(b>maxs)maxs=b;
  if(a>(1ULL<<62)||b>(1ULL<<62)){printf("OVERFLOW at %llu\n",i);return 1;}
  if(((i&(i-1))==0 && i>1000000)) printf("visit %llu a=%llu b=%llu max=%llu steps~%.3Le\n",i,a,b,maxs,steps);
 } printf("done %.0f visits no halt, a=%llu b=%llu max=%llu steps~%.4Le\n",N,a,b,maxs,steps);}
