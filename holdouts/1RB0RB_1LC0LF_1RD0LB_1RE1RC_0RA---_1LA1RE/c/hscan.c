#include "../../../tools/c/tm.h"
/* hscan (build: gcc -O2 -o hscan hscan.c from this folder) MACHINE PREFIX WORD SUFFIX YFROM YTO STATE COEF: tape PREFIX WORD^y SUFFIX, head on last cell in STATE;
   prints y and the step count (bbchallenge count) for each y that halts within COEF*y*y + 100000 steps */
int main(int argc,char**argv){ tm_machine m; tm_parse(argv[1],&m);
 const char*pre=argv[2],*w=argv[3],*suf=argv[4]; long long y0=atoll(argv[5]),y1=atoll(argv[6]); int st0=argv[7][0]-'A'; double coef=atof(argv[8]);
 for(long long y=y0;y<y1;y++){ tm_tape t; tm_tape_init(&t,1<<16); long long p=0;
  for(const char*c=pre;*c;c++){ if(*c=='0'||*c=='1'){ while(p+t.off>=t.size) tm_grow(&t); t.c[p+t.off]=*c-'0'; p++;} }
  for(long long k=0;k<y;k++) for(const char*c=w;*c;c++){ while(p+t.off>=t.size) tm_grow(&t); t.c[p+t.off]=*c-'0'; p++;}
  for(const char*c=suf;*c;c++){ if(*c=='0'||*c=='1'){ while(p+t.off>=t.size) tm_grow(&t); t.c[p+t.off]=*c-'0'; p++;} }
  t.lo=0; t.hi=p-1; t.head=p-1; int st=st0; long long k=0; int halted=0;
  long long max=(long long)(coef*(double)y*(double)y)+100000; while(k<max){ k++; if(!tm_step(&m,&t,&st)){halted=1;break;} }
  if(halted) {printf("%lld HALT %lld\n",y,k); fflush(stdout);}
  tm_tape_free(&t);}
 return 0;}
