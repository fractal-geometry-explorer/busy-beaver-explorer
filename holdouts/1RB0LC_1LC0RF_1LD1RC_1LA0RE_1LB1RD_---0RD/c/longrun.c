// longrun MACHINE MAXSTEPS: print "steps ones lo hi" at 1e6,1e7,... and every 1e10; final line halted/running
#include "../../../tools/c/tm.h"
int main(int argc,char**argv){tm_machine m; tm_parse(argv[1],&m); long long N=atoll(argv[2]);
 tm_tape t; tm_tape_init(&t,1<<20); int st=0; long long k=0, next=1000000; int halted=0;
 while(k<N){ long long chunk = next-k; if(chunk>N-k) chunk=N-k; int h=0; long long d=tm_run(&m,&t,&st,chunk,&h); k+=d; if(h){halted=1;break;}
   if(k==next){ printf("%lld %lld %lld %lld\n",k,tm_ones(&t),t.lo,t.hi); fflush(stdout); next = next<10000000000LL? next*10 : next+10000000000LL; } }
 printf("%s %lld %lld %lld %lld\n",halted?"halted":"running",k,tm_ones(&t),t.lo,t.hi); }
