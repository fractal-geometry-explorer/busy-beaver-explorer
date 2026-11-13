/* gapdump: the gap counter of 1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD read off the real machine.
 *
 *   gcc -O2 -o gapdump holdouts/1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD/c/gapdump.c && ./gapdump 20000000000 > m2g.txt
 *
 * At every sample point (head in C on the fourth cell from the left end, coming from the right, about to move
 * right, the three cells to its left all 1) it prints "STEP Z| g^k g^k ... |T": Z zeros from the head to the first
 * 1, then the gaps between consecutive 1s run-length coded, then T zeros after the last 1.  The model expects Z = 2,
 * T = 0 (the configuration `cfg` of lean/Counter.lean).  `py/model.py check m2g.txt` compares it with the model.
 * Optional second argument: print only every k-th sample.
 */
#include "../../../tools/c/tm.h"
int main(int argc,char**argv){
  tm_machine m; tm_parse("1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD",&m);
  long long to=atoll(argv[1]); long long every=argc>2?atoll(argv[2]):1;
  tm_tape t; tm_tape_init(&t,1<<20); int st=0; long long k=0, prev=0, nb=0;
  while(k<to){
    long long h=t.head;
    int r=tm_get(&t,h);
    if(st==2 && h==t.lo+3 && prev==h+1 && m.d[2][r]>0 && tm_get(&t,t.lo)==1&&tm_get(&t,t.lo+1)==1&&tm_get(&t,t.lo+2)==1){
      nb++;
      if(nb%every==0){
      printf("%lld",k);
      long long p=h; long long z=0; while(p<=t.hi&&tm_get(&t,p)==0){z++;p++;}
      printf(" %lld|",z);
      long long lastg=-1,cnt=0;
      while(p<=t.hi){ /* p at a 1 */
        long long q=p+1; long long gz=0; while(q<=t.hi&&tm_get(&t,q)==0){gz++;q++;}
        if(q>t.hi){ /* trailing */ if(cnt) printf(" %lld^%lld",lastg,cnt); printf(" |%lld\n",gz); break;}
        if(gz==lastg) cnt++; else { if(cnt) printf(" %lld^%lld",lastg,cnt); lastg=gz; cnt=1; }
        p=q;
      }
      }
    }
    prev=h;
    if(!tm_step(&m,&t,&st)){printf("%lld HALT\n",k+1);return 0;}
    k++;
  }
  return 0;
}
