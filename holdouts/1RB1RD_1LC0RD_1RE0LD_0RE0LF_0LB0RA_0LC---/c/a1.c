/* a1 MACHINE MAX: every step where A reads a 1 (the only place the twins differ), with the leftmost 40 cells. */
#include "../../../tools/c/tm.h"
int main(int argc,char**argv){ tm_machine m; tm_parse(argv[1],&m); long long b=atoll(argv[2]);
 tm_tape t; tm_tape_init(&t,1<<16); int st=0; long long k=0;
 while(k<b){ if(st==0 && tm_get(&t,t.head)==1){ printf("%lld A1 at offset %lld from left end, width %lld:",k,t.head-t.lo,t.hi-t.lo+1); for(long long q=t.lo;q<t.lo+40;q++) putchar('0'+tm_get(&t,q)); putchar('\n'); fflush(stdout);} k++; if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);return 0;} } }
