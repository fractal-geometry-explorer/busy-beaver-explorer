#include "../../../tools/c/tm.h"
/* trlog MACHINE N S Y [full]: log each use of transition (S,Y): step, pos-lo, hi-pos, [tape] */
int main(int argc,char**argv){tm_machine m; tm_parse(argv[1],&m); long long n=atoll(argv[2]); int S=argv[3][0]-'A', Y=atoi(argv[4]); int full=argc>5;
 tm_tape t; tm_tape_init(&t,1<<20); int st=0;
 for(long long k=0;k<n;k++){ int y=tm_get(&t,t.head); if(st==S&&y==Y){ printf("%lld %lld %lld",k,t.head-t.lo,t.hi-t.head); if(full){putchar(' '); for(long long p=t.lo;p<=t.hi;p++) putchar(p==t.head? (tm_get(&t,p)?'I':'O') : '0'+tm_get(&t,p));} putchar('\n');}
  if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k+1);break;} }
}
