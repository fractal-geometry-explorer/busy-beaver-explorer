#include "../../../tools/c/tm.h"
// sweeps MACHINE FROM TO MINLEN: print turning points of excursions longer than MINLEN between steps FROM and TO
int main(int argc,char**argv){tm_machine m;tm_parse(argv[1],&m);long long A=atoll(argv[2]),B=atoll(argv[3]),ML=atoll(argv[4]);
tm_tape t;tm_tape_init(&t,1<<20);int st=0;
long long ext=0; int dir=0; long long extstep=0; int extst=0; long long last=0;
for(long long i=1;i<=B;i++){long long h0=t.head;if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",i);return 0;}
 long long h=t.head;
 if(dir>=0){ if(h>ext||dir==0){ext=h;extstep=i;extst=st;dir=1;} else if(ext-h>ML){ if(i>A) printf("%lld R %lld %c lo=%lld hi=%lld\n",extstep,ext,'A'+extst,t.lo,t.hi); dir=-1; ext=h;extstep=i;extst=st;} }
 else { if(h<ext){ext=h;extstep=i;extst=st;} else if(h-ext>ML){ if(i>A) printf("%lld L %lld %c\n",extstep,ext,'A'+extst); dir=1; ext=h;extstep=i;extst=st;} }
}
return 0;}
