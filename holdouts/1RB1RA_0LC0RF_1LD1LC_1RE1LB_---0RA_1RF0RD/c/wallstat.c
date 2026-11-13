/* wallstat MACHINE STEPS: counts the extensions of the tape at each end by state; at each power-of-two count of right
   extensions prints the step, state, the length of the run of 1s left of the head and the width.
   gcc -O2 -o wallstat wallstat.c && ./wallstat 1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD 20000000000 */
#include "../../../tools/c/tm.h"
int main(int argc,char**argv){
  tm_machine m; tm_parse(argv[1],&m); long long max=atoll(argv[2]);
  tm_tape t; tm_tape_init(&t,1<<16); int st=0; long long k=0; long long rv[8]={0},lv[8]={0}; long long nr=0, next=1;
  long long maxrun=0;
  while(k<max){ long long lo=t.lo,hi=t.hi; k++; if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);break;}
    if(t.hi>hi){ rv[st]++; nr++;
      long long p=t.head-1,r=0; while(p>=t.lo && tm_get(&t,p)==1){r++;p--;} if(r>maxrun)maxrun=r;
      if(nr==next){printf("visit %lld step %lld state %c run %lld width %lld\n",nr,k,'A'+st,r,t.hi-t.lo);next*=2;fflush(stdout);} }
    if(t.lo<lo) lv[st]++;
  }
  printf("steps %lld right-extensions by state:",k); for(int i=0;i<6;i++)printf(" %c=%lld",'A'+i,rv[i]);
  printf("  left-extensions:"); for(int i=0;i<6;i++)printf(" %c=%lld",'A'+i,lv[i]); printf(" maxrun %lld\n",maxrun);
}
