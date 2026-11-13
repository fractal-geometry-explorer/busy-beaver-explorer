#include "../../../tools/c/tm.h"
/* turns MACHINE FROM TO: prints raw tape at each head reversal */
int main(int argc,char**argv){tm_machine m; tm_parse(argv[1],&m); long long from=atoll(argv[2]), to=atoll(argv[3]);
 tm_tape t; tm_tape_init(&t,1<<20); int st=0; long long k=0; long long ph=0; int ld=0;
 while(k<to){ long long h0=t.head; k++; if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);break;}
  int d=t.head>h0?1:-1;
  if(d!=ld && k>=from){ printf("%12lld %4lld %c ",k,t.head-t.lo,'A'+st); for(long long p=t.lo;p<=t.hi;p++) putchar(p==t.head? (tm_get(&t,p)?'I':'O') : '0'+tm_get(&t,p)); putchar('\n');}
  ld=d; }
}
