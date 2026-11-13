/* print left part (abs lo..0) each time state D reads 0 at abs 1 */
#include "../../../tools/c/tm.h"
int main(int argc,char**argv){
  tm_machine m; tm_parse(argv[1],&m); long long max=atoll(argv[2]);
  tm_tape t; tm_tape_init(&t,1<<16); int st=0; long long k=0;
  while(k<max){ k++;
    if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);break;}
    if(st==3 && t.head==1 && tm_get(&t,1)==0){ printf("%lld ",k); for(long long p=t.lo;p<=0;p++) putchar('0'+tm_get(&t,p)); putchar('\n'); }
  }
}
