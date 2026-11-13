#include "../../../tools/c/tm.h"
// snap MACHINE W step1 step2 ... : print tape cells lo..lo+W at given steps (sorted)
int main(int argc,char**argv){tm_machine m;tm_parse(argv[1],&m);long long W=atoll(argv[2]);
tm_tape t;tm_tape_init(&t,1<<20);int st=0;long long i=0;
for(int a=3;a<argc;a++){long long S=atoll(argv[a]); while(i<S){i++; if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",i);return 0;}}
 printf("%lld %lld %lld %lld %c ",i,t.lo,t.hi,t.head,'A'+st); long long e=t.lo+W; if(e>t.hi)e=t.hi; for(long long p=t.lo;p<=e;p++){ if(p==t.head)putchar('>'); putchar('0'+tm_get(&t,p));} putchar('\n');}
return 0;}
