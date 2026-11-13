/* cdump: the counter of 1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB--- read off the real machine.
 *
 *   gcc -O2 -o cdump holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/c/cdump.c && ./cdump 4000000000 1 > m1c.txt
 *
 * At every visit of the head, in C, to the left end of the tape it parses the tape as
 *   C> 0 10 x^n0 [1 a^d x^n]... 1     (x = 1110, a = 10)
 * and prints "STEP C n0 : d,n d,n ... 0,0" (the last 0,0 is the final 1; "C ?" if the tape has another shape).
 * At every right extension it prints the blocks of pairs 10 between single 1s: "STEP R STATE x1 | x2 ...".
 * `py/model.py check` compares the counter lines with the model.
 */
#include "../../../tools/c/tm.h"
static int g(tm_tape*t,long long p){return tm_get(t,p);}
static int isx(tm_tape*t,long long p){return p+3<=t->hi&&g(t,p)==1&&g(t,p+1)==1&&g(t,p+2)==1&&g(t,p+3)==0;}
static int isa(tm_tape*t,long long p){return p+1<=t->hi&&g(t,p)==1&&g(t,p+1)==0;}
int main(int argc,char**argv){
  tm_machine m; tm_parse(argc>3?argv[3]:"1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---",&m);
  long long to=atoll(argv[1]); int every=atoi(argv[2]);
  tm_tape t; tm_tape_init(&t,1<<20); int st=0; long long k=0, nb=0;
  while(k<to){
    long long oh=t.hi;
    if(!tm_step(&m,&t,&st)){printf("%lld HALT\n",k+1);return 0;}
    k++;
    if(t.hi>oh){ /* right extension */
      printf("%lld R %c",k,'A'+st);
      long long p=t.lo; while(p<=t.hi){ long long c=0; while(p<=t.hi&&isa(&t,p)){c++;p+=2;} printf(" %lld",c); if(p<=t.hi){ if(g(&t,p)==1){printf(" |");p++;} else {printf(" _");p++;} } }
      printf("\n");
    }
    if(t.head==t.lo&&st==2){
      nb++; if(every==0 || nb%every) continue;
      long long p=t.head;
      if(!(g(&t,p)==0&&g(&t,p+1)==1&&g(&t,p+2)==0)){printf("%lld C ?\n",k);continue;}
      p+=3; long long n0=0; while(isx(&t,p)){n0++;p+=4;}
      printf("%lld C %lld :",k,n0);
      while(p<=t.hi && g(&t,p)==1){ p++; int d=0; while(isa(&t,p)&&!isx(&t,p)){d++;p+=2;} long long n=0; while(isx(&t,p)){n++;p+=4;} printf(" %d,%lld",d,n); }
      if(p<=t.hi) printf(" REST@%lld",t.hi-p+1);
      printf("\n");
    }
  }
  return 0;
}
