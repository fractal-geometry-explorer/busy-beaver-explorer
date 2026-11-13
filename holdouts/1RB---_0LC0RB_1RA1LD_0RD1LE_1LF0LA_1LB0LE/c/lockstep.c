#include "../../../tools/c/tm.h"
/* lockstep M1 M2 N: run both, compare head position and the written symbol at every step, and the state whenever
   it is not the step after the differing transition; report first difference */
int main(int argc,char**argv){tm_machine a,b; tm_parse(argv[1],&a); tm_parse(argv[2],&b); long long n=atoll(argv[3]);
 tm_tape ta,tb; tm_tape_init(&ta,1<<20); tm_tape_init(&tb,1<<20); int sa=0,sb=0; long long statediff=0;
 for(long long k=1;k<=n;k++){ int ya=tm_get(&ta,ta.head), yb=tm_get(&tb,tb.head);
  if(ya!=yb||ta.head!=tb.head){printf("differ at step %lld\n",k);return 0;}
  int ha=tm_step(&a,&ta,&sa), hb=tm_step(&b,&tb,&sb); if(!ha||!hb){printf("halt at %lld (%d %d)\n",k,ha,hb);return 0;}
  if(sa!=sb) statediff++; }
 printf("same head and tape for %lld steps; states differed after %lld steps (each time healed on the next step)\n",n,statediff);
}
