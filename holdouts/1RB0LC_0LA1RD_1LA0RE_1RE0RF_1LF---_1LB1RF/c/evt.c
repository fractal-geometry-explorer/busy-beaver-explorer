/* evt M N STATE SYM A B: at each time STATE reads SYM, print step, head-lo, hi-head and cells [head-A, head+B] */
#include "../../../tools/c/tm.h"
int main(int argc,char**argv){tm_machine m; tm_parse(argv[1],&m); long long N=atoll(argv[2]);
 int S=argv[3][0]-'A', Y=atoi(argv[4]), A=atoi(argv[5]), B=atoi(argv[6]);
 tm_tape t; tm_tape_init(&t,1<<16); int st=0;
 for(long long k=0;k<N;k++){ int y=tm_get(&t,t.head);
  if(st==S&&y==Y){ printf("%lld %lld %lld ",k,t.head-t.lo,t.hi-t.head); for(long long p=t.head-A;p<=t.head+B;p++){ if(p==t.head)putchar('['); putchar((p<t.lo||p>t.hi)?'.':'0'+tm_get(&t,p)); if(p==t.head)putchar(']');} putchar('\n'); }
  if(!tm_step(&m,&t,&st)){printf("halted at %lld\n",k+1);break;} }
}
