/* abres.c: residues (a mod M, g mod M) of near-diagonal visits (b > a, g = b - a <= G) of the A(a,b) orbit; usage: abres N G M */
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
static unsigned long long c[256][256];
int main(int argc,char**argv){
  unsigned long long N=strtoull(argv[1],0,10),G=strtoull(argv[2],0,10); int M=atoi(argv[3]);
  u128 a=2,b=9;
  for(unsigned long long i=0;i<N;i++){
    if(b>a && b-a<=G) c[(int)(a%M)][(int)((b-a)%M)]++;
    if(b==3){printf("HALT\n");return 0;}
    else if(b==2){a-=3;b=7;}
    else if(a>=b){a=a-b+1;b=2*b+3;}
    else if(b==a+1){b=2*a+4;a=4;}
    else if(b==a+2){b=2*a+7;a=1;}
    else if((a&1)&&b==a+3){a=2*a+1;b=9;}
    else if(!(a&1)){b=b-a-1;a=2*a+4;}
    else{b=b-a;a=2*a+3;}
  }
  for(int x=0;x<M;x++){printf("a=%2d:",x);for(int y=0;y<M;y++)printf(" %6llu",c[x][y]);printf("\n");}
}
