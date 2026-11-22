/* abdig.c: the swap/grow digits of the A(a,b) orbit (1 = swap, 0 = grow) and a + b along it.
   Counts the blocks of L consecutive digits over the first N visits (chi-square against 2^-L each) and the
   increments of s = a + b by rule.  usage: abdig N L */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef unsigned __int128 u128;
int main(int argc,char**argv){
  unsigned long long N=strtoull(argv[1],0,10); int L=atoi(argv[2]);
  unsigned long long *c=calloc(1u<<L,8), inc[10]={0}; unsigned w=0, mask=(1u<<L)-1;
  u128 a=2,b=9; unsigned long long nb=0;
  for(unsigned long long i=0;i<N;i++){
    u128 s0=a+b; int d;
    if(b==3){printf("HALT\n");return 0;}
    else if(b==2){a-=3;b=7;d=0;}
    else if(a>=b){a=a-b+1;b=2*b+3;d=1;}
    else if(b==a+1){b=2*a+4;a=4;d=0;}
    else if(b==a+2){b=2*a+7;a=1;d=0;}
    else if((a&1)&&b==a+3){a=2*a+1;b=9;d=0;}
    else if(!(a&1)){b=b-a-1;a=2*a+4;d=0;}
    else{b=b-a;a=2*a+3;d=0;}
    int ds=(int)(a+b-s0); if(ds>=0&&ds<10) inc[ds]++; else printf("odd increment %d\n",ds);
    w=((w<<1)|d)&mask; if(i>=(unsigned long long)L){c[w]++;nb++;}
  }
  double e=(double)nb/(1u<<L), chi=0; unsigned long long mn=~0ULL,mx=0;
  for(unsigned k=0;k<=mask;k++){double x=c[k]-e; chi+=x*x/e; if(c[k]<mn)mn=c[k]; if(c[k]>mx)mx=c[k];}
  printf("blocks of %d digits: %u kinds, expected %.1f each, min %llu max %llu, chi2 %.1f (df %u)\n",L,mask+1,e,mn,mx,chi,mask);
  printf("final a+b = "); { u128 s=a+b; char t[50]; int i=49; t[i]=0; while(s){t[--i]='0'+(int)(s%10); s/=10;} printf("%s, per visit %.6f\n",t+i,(double)(a+b)/N); }
  for(int k=0;k<10;k++) if(inc[k]) printf("a+b grows by %d: %llu visits\n",k,inc[k]);
}
