/* seppos.c: at each bounce (the head at the left end of the visited tape, turning right) print the step, lo, hi
   and the positions of all cells not inside a run of 10s (read greedily from lo), with . for 0 and * for 1:
   the left-end 0, the single-0 separators and the two cells of each wall.  Input for py/spcheck.py.
   usage: gcc -O2 -I tools/c -o seppos c/seppos.c && ./seppos MACHINE MAXSTEPS FROMSTEP */
/* at each left-end bounce print step, lo, and the absolute positions+bits of all cells not inside a "10" run (parsed greedily from lo) */
#include "tm.h"
int main(int argc,char**argv){
  tm_machine m; tm_parse(argv[1],&m); long long max=atoll(argv[2]); long long from=atoll(argv[3]);
  tm_tape t; tm_tape_init(&t,1<<22); int st=0; int dir=1;
  for(long long k=1;k<=max;k++){ long long h=t.head;
    if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);return 0;}
    int d=t.head>h?1:-1;
    if(d!=dir && d>0 && h==t.lo && k>=from){
      printf("%lld %lld %lld:",k,t.lo,t.hi);
      long long p=t.lo,e=t.hi;
      while(p<=e){ if(p+1<=e && tm_get(&t,p)==1&&tm_get(&t,p+1)==0){p+=2;continue;} printf(" %lld%c",p,tm_get(&t,p)?'*':'.'); p++; }
      printf("\n"); }
    dir=d; }
}
