#include "../../../tools/c/tm.h"
/* sampg MACHINE START SAMPLESTATE RA RB MAX [FROM]: at each step where the head is at lo, reading 0, in SAMPLESTATE (original orientation),
   print "S step blocks": the mirrored cells hi..lo+1 (leading zeros stripped) as 1^a0^b blocks, runs of (RA,RB) as Pn. */
int main(int argc,char**argv){ tm_machine m; tm_parse(argv[1],&m); int st=argv[2][0]-'A'; int Q=argv[3][0]-'A'; int RA=atoi(argv[4]),RB=atoi(argv[5]);
 long long max=atoll(argv[6]), from=argc>7?atoll(argv[7]):0;
 tm_tape t; tm_tape_init(&t,1<<22); long long k=0;
 while(k<max){ k++; if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);fflush(stdout);return 0;}
  if(st==Q && t.head==t.lo && tm_get(&t,t.head)==0 && k>=from){ printf("S %lld",k); long long p=t.hi; while(p>t.lo && !tm_get(&t,p)) p--;
     long long run=0;
     while(p>t.lo){ long long a=0,b=0; while(p>t.lo&&tm_get(&t,p)){a++;p--;} while(p>t.lo&&!tm_get(&t,p)){b++;p--;}
        if(a==RA&&b==RB){run++;continue;} if(run){printf(" P%lld",run);run=0;} printf(" %lld/%lld",a,b);} if(run)printf(" P%lld",run); printf("\n"); }
 }
 printf("END %lld\n",k); return 0;}
