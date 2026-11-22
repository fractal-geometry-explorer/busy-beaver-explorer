/* abrand.c: from many random starts A(a, b) (a, b uniform below S), run each orbit L visits (or to b = 3) and count
   visits with b - a = g for g = 1..8 by parity of a; halts (b = 3) are counted too.
   usage: abrand SEED STARTS L S [v]     (v: print each start that halts) */
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
static unsigned long long x=88172645463325252ULL;
static unsigned long long rnd(void){x^=x<<13;x^=x>>7;x^=x<<17;return x;}
int main(int argc,char**argv){
  x^=strtoull(argv[1],0,10)*0x9E3779B97F4A7C15ULL; long K=atol(argv[2]); unsigned long long L=strtoull(argv[3],0,10), S=strtoull(argv[4],0,10);
  unsigned long long c[9][2]={{0}}, halts=0, b2=0, tot=0;
  for(long t=0;t<K;t++){
    u128 a=1+rnd()%S, b=4+rnd()%S, a0=a, b0=b;
    for(unsigned long long i=0;i<L;i++){
      tot++;
      if(b>a && b-a<=8) c[(int)(b-a)][(int)(a&1)]++;
      if(b==3){halts++; if(argc>5) printf("halt start=(%llu,%llu) visits=%llu\n",(unsigned long long)a0,(unsigned long long)b0,i); break;}
      else if(b==2){b2++;a-=3;b=7;}
      else if(a>=b){a=a-b+1;b=2*b+3;}
      else if(b==a+1){b=2*a+4;a=4;}
      else if(b==a+2){b=2*a+7;a=1;}
      else if((a&1)&&b==a+3){a=2*a+1;b=9;}
      else if(!(a&1)){b=b-a-1;a=2*a+4;}
      else{b=b-a;a=2*a+3;}
    }
  }
  printf("visits %llu halts %llu b2 %llu\n",tot,halts,b2);
  for(int g=1;g<=8;g++) printf("g=%d a-even %llu a-odd %llu\n",g,c[g][0],c[g][1]);
}
