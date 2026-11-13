#include "../../../tools/c/tm.h"
/* hist2 MACHINE FROM TO: best (pos,state) of turns: the position/state with max count; prints "pos state count" */
int main(int argc,char**argv){tm_machine m; tm_parse(argv[1],&m); long long from=atoll(argv[2]), to=atoll(argv[3]);
 tm_tape t; tm_tape_init(&t,1<<20); int st=0; long long k=0; int ld=0; static long long H[8192][10]; long long base=0; int set=0;
 while(k<to){ long long h0=t.head; k++; if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);return 0;}
  int d=t.head>h0?1:-1;
  if(k>=from){ if(!set){base=t.lo;set=1;} if(d!=ld){ long long p=t.head-base+1000; if(p>=0&&p<8192) H[p][st]++; } }
  ld=d; }
 long long b=0; int bp=0,bs=0; for(int p=0;p<8192;p++) for(int q=0;q<10;q++) if(H[p][q]>b){b=H[p][q];bp=p;bs=q;}
 printf("%d %c %lld\n",bp-1000,'A'+bs,b);
}
