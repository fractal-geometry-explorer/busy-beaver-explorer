/* lcnt MACHINE MAX WINDOW PREFIX: decode the left binary counter (PREFIX cells after the first 1, then 4-cell digits
   1010 = 1 / 1000 = 0, then 11) whenever the head is 118 cells right of the left end, and print per WINDOW steps:
   increments, steps and F visits per increment, overflows, value, digits and tape width.  2a: PREFIX 16, 2b: 2. */
#include "../../../tools/c/tm.h"
/* left counter decoder: prefix length P (cells), digits 1010=1 / 1000=0 until "11". Window stats. */
int main(int argc,char**argv){ tm_machine m; tm_parse(argv[1],&m); long long b=atoll(argv[2]),W=atoll(argv[3]); int P=atoi(argv[4]); int Wd=110;
 tm_tape t; tm_tape_init(&t,1<<16); int st=0; long long k=0; int dirty=1; unsigned long long lastv=0; int lastb=-1; long long inc=0,ovf=0,oth=0,nf=0;
 while(k<b){ k++; long long h=t.head; if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);return 0;}
   if(st==5) nf++;
   if(h-t.lo < Wd+8) dirty=1;
   if(dirty && t.head-t.lo >= Wd+8){ dirty=0;
     long long p=t.lo; while(tm_get(&t,p)==0) p++; p+=P; unsigned long long v=0; int bb=0;
     while(tm_get(&t,p)==1&&tm_get(&t,p+1)==0&&tm_get(&t,p+3)==0){ v=v*2+tm_get(&t,p+2); bb++; p+=4; }
     if(tm_get(&t,p)==1&&tm_get(&t,p+1)==1){
       if(lastb>=0 && (v!=lastv||bb!=lastb)){ if(bb==lastb&&v>lastv) inc++; else if(bb>lastb) {ovf++; printf("  overflow at %lld: %d -> %d digits\n",k,lastb,bb);} else oth++; }
       lastv=v; lastb=bb; } }
   if(k%W==0){ printf("%lld inc %lld steps/inc %.1f F/inc %.2f ovf %lld other %lld value %llu digits %d width %lld\n",k,inc,inc?(double)W/inc:0,inc?(double)nf/inc:0,ovf,oth,lastv,lastb,t.hi-t.lo+1); fflush(stdout); inc=0;ovf=0;oth=0;nf=0; } } }
