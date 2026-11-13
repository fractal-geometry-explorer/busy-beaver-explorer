/* longrun MACHINE STEPS: direct simulation, prints halted/running, steps, ones, lo, hi, every 1e10 progress */
#include "../../../tools/c/tm.h"
int main(int argc,char**argv){ tm_machine m; tm_parse(argv[1],&m); long long N=atoll(argv[2]);
 tm_tape t; tm_tape_init(&t,1<<22); int st=0,h; long long k=0, chunk=10000000000LL;
 while(k<N){ long long n=N-k<chunk?N-k:chunk; long long r=tm_run(&m,&t,&st,n,&h); k+=r; if(h){printf("halted %lld\n",k);return 0;}
   printf("at %lld lo %lld hi %lld\n",k,t.lo,t.hi); fflush(stdout);}
 printf("running %lld ones %lld lo %lld hi %lld state %c\n",k,tm_ones(&t),t.lo,t.hi,'A'+st); return 0;}
