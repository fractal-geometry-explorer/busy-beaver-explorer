#include "../../../tools/c/tm.h"
/* raw MACHINE MAX mode: prints raw tape at each time head is at lo or hi (mode e), with state */
int main(int argc,char**argv){tm_machine m; tm_parse(argv[1],&m); long long max=atoll(argv[2]); long long from=argc>3?atoll(argv[3]):0;
 tm_tape t; tm_tape_init(&t,1<<20); int st=0; long long k=0; int last=0;
 while(k<max){ k++; if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);break;}
  int e = t.head==t.lo? -1 : t.head==t.hi? 1:0;
  if(e && e!=last && k>=from){ printf("%12lld %c%c ",k,e<0?'L':'R','A'+st); for(long long p=t.lo;p<=t.hi;p++) putchar(p==t.head? (tm_get(&t,p)?'I':'O') : '0'+tm_get(&t,p)); putchar('\n');}
  if(e) last=e; }
}
