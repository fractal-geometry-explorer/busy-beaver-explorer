#include "../../../tools/c/tm.h"
int main(int argc,char**argv){tm_machine m; tm_parse(argv[1],&m); long long from=atoll(argv[2]), to=atoll(argv[3]), ev=atoll(argv[4]);
 tm_tape t; tm_tape_init(&t,1<<20); int st=0; long long k=0;
 while(k<to){ k++; if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);break;}
  if(k>=from && (k-from)%ev==0){ printf("%lld %c ",k,'A'+st); for(long long p=t.lo;p<=t.hi;p++) putchar(p==t.head? (tm_get(&t,p)?'I':'O') : '0'+tm_get(&t,p)); putchar('\n');} }
}
