/* edge M N SIDE EVERY: print the whole tape (with the head state) each EVERY-th time the head reaches a fresh cell
   on SIDE (L or R): "step state tape" with the head cell marked by brackets. */
#include "../../../tools/c/tm.h"
int main(int argc,char**argv){tm_machine m; tm_parse(argv[1],&m); long long N=atoll(argv[2]); int R=argv[3][0]=='R';
 long long E=atoll(argv[4]); tm_tape t; tm_tape_init(&t,1<<16); int st=0; long long lo0=0,hi0=0,cnt=0;
 for(long long k=0;k<N;k++){
  if((R&&t.head>hi0)||(!R&&t.head<lo0)){ if(R)hi0=t.head; else lo0=t.head; if(++cnt%E==0){
    printf("%lld %c ",k,'A'+st); for(long long p=t.lo;p<=t.hi;p++){ if(p==t.head)putchar('['); putchar('0'+tm_get(&t,p)); if(p==t.head)putchar(']');} putchar('\n');}}
  if(!tm_step(&m,&t,&st)){printf("halted at %lld\n",k+1);break;} }
}
