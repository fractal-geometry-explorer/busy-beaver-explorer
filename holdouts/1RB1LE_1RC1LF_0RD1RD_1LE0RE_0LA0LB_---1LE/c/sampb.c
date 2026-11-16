#include "../../../tools/c/tm.h"
/* sampb MACHINE START MAX [FROM]: at each visit of lo in state E (original orientation), print
   "S step blocks" where blocks are the mirrored cells hi..lo+1 (leading zeros stripped) as 1^a0^b blocks, runs of (2,1) as Pn.
   Also prints "R step" when the head reaches hi in state E reading 0 at the right end (the overflow visit). */
int main(int argc,char**argv){ tm_machine m; tm_parse(argv[1],&m); int st=argv[2][0]-'A'; long long max=atoll(argv[3]), from=argc>4?atoll(argv[4]):0;
 tm_tape t; tm_tape_init(&t,1<<22); long long k=0;
 while(k<max){ k++; if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);fflush(stdout);return 0;}
  if(st==4 && t.head==t.lo && tm_get(&t,t.head)==0 && k>=from){ printf("S %lld",k); long long p=t.hi; while(p>t.lo && !tm_get(&t,p)) p--;
     long long run=0;
     while(p>t.lo){ long long a=0,b=0; while(p>t.lo&&tm_get(&t,p)){a++;p--;} while(p>t.lo&&!tm_get(&t,p)){b++;p--;}
        if(a==2&&b==1){run++;continue;} if(run){printf(" P%lld",run);run=0;} printf(" %lld/%lld",a,b);} if(run)printf(" P%lld",run); printf("\n"); }
  else if(st==4 && t.head==t.hi && tm_get(&t,t.head)==0 && k>=from) printf("R %lld\n",k);
 }
 printf("END %lld\n",k); return 0;}
