/* print the leftmost W cells (from lo) whenever they changed since the last print and the head is at least W cells right of lo */
#include "../../../tools/c/tm.h"
int main(int argc,char**argv){
  tm_machine m; tm_parse(argv[1],&m); long long max=atoll(argv[2]); int W=atoi(argv[3]);
  tm_tape t; tm_tape_init(&t,1<<16); int st=0; long long k=0; static char cur[100000], prev[100000]; int dirty=1;
  while(k<max){ k++; long long h=t.head;
    if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);break;}
    if(h-t.lo < W+8) dirty=1;
    if(dirty && t.head-t.lo >= W+8){ for(int i=0;i<W;i++) cur[i]='0'+tm_get(&t,t.lo+i); cur[W]=0; dirty=0;
       if(strcmp(cur,prev)){ strcpy(prev,cur); printf("%lld %lld %s\n",k,t.lo,cur);} }
  }
}
