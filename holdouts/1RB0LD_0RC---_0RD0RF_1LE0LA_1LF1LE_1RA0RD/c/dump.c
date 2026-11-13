#include "../../../tools/c/tm.h"
// dump MACHINE MAXSTEPS EVERYREC : at every EVERYREC-th right record print step lo hi head state and tape as 0/1 string
int main(int argc,char**argv){tm_machine m;tm_parse(argv[1],&m);long long N=atoll(argv[2]);long long E=atoll(argv[3]);
tm_tape t;tm_tape_init(&t,1<<20);int st=0;long long hi=0,rc=0;
for(long long i=1;i<=N;i++){if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",i);return 0;}
 if(t.hi>hi){hi=t.hi; if(++rc%E==0){printf("%lld %lld %lld %c ",i,t.lo,t.hi,'A'+st);for(long long p=t.lo;p<=t.hi;p++)putchar('0'+tm_get(&t,p));putchar('\n');}}}
return 0;}
