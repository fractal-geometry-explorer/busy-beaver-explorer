/* abstat.c: near-diagonal statistics of the A(a,b) orbit from (2,9): for b > a with g = b - a <= G, count by
   (parity of a, parity of g) and by decade of the visit index.  usage: abstat N G */
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
int main(int argc,char**argv){
  unsigned long long N=strtoull(argv[1],0,10); unsigned long long G=strtoull(argv[2],0,10);
  u128 a=2,b=9; unsigned long long c[20][2][2]={{{0}}}; unsigned long long dec=10; int d=0;
  for(unsigned long long i=0;i<N;i++){
    if(i==dec){d++;dec*=10;}
    if(b>a && b-a<=G) c[d][(int)(a&1)][(int)((b-a)&1)]++;
    if(b==3){printf("HALT %llu\n",i);return 0;}
    else if(b==2){a-=3;b=7;}
    else if(a>=b){a=a-b+1;b=2*b+3;}
    else if(b==a+1){b=2*a+4;a=4;}
    else if(b==a+2){b=2*a+7;a=1;}
    else if((a&1)&&b==a+3){a=2*a+1;b=9;}
    else if(!(a&1)){b=b-a-1;a=2*a+4;}
    else{b=b-a;a=2*a+3;}
  }
  printf("decade  a-even/g-even a-even/g-odd a-odd/g-even a-odd/g-odd  (counts with g<=%llu)\n",G);
  for(int k=0;k<=d;k++) printf("1e%d..1e%d  %llu %llu %llu %llu\n",k,k+1,c[k][0][0],c[k][0][1],c[k][1][0],c[k][1][1]);
}
