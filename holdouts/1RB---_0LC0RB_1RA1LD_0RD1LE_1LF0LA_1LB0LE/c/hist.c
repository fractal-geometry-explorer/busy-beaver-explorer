#include "../../../tools/c/tm.h"
/* hist MACHINE FROM TO: histogram of turn positions (relative to lo at FROM) by state */
int main(int argc,char**argv){tm_machine m; tm_parse(argv[1],&m); long long from=atoll(argv[2]), to=atoll(argv[3]);
 tm_tape t; tm_tape_init(&t,1<<20); int st=0; long long k=0; int ld=0; static long long H[4096][10]; long long base=0; int set=0;
 while(k<to){ long long h0=t.head; k++; if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);break;}
  int d=t.head>h0?1:-1;
  if(k>=from){ if(!set){base=t.lo;set=1;} if(d!=ld){ long long p=t.head-base+100; if(p>=0&&p<4096) H[p][st]++; } }
  ld=d; }
 for(int p=0;p<4096;p++){ long long s=0; for(int q=0;q<10;q++) s+=H[p][q]; if(s){ printf("%d %lld :",p-100,s); for(int q=0;q<m.n;q++) if(H[p][q]) printf(" %c%lld",'A'+q,H[p][q]); printf("\n");}}
}
