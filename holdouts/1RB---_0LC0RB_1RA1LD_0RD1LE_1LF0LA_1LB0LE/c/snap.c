#include "../../../tools/c/tm.h"
/* snap MACHINE FROM TO POS STATE EVERY: print raw tape when a turn happens at POS (rel. lo at FROM) in STATE; every EVERY-th */
int main(int argc,char**argv){tm_machine m; tm_parse(argv[1],&m); long long from=atoll(argv[2]), to=atoll(argv[3]); long long pos=atoll(argv[4]); int S=argv[5][0]-'A'; long long ev=atoll(argv[6]);
 tm_tape t; tm_tape_init(&t,1<<20); int st=0; long long k=0; int ld=0; long long base=0; int set=0; long long cnt=0;
 while(k<to){ long long h0=t.head; k++; if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);break;}
  int d=t.head>h0?1:-1;
  if(k>=from){ if(!set){base=t.lo;set=1;} if(d!=ld && t.head-base==pos && st==S){ if(cnt++%ev==0){ printf("%lld %c ",k,'A'+st); for(long long p=t.lo;p<=t.hi;p++) putchar(p==t.head? (tm_get(&t,p)?'I':'O') : '0'+tm_get(&t,p)); putchar('\n');}} }
  ld=d; }
}
