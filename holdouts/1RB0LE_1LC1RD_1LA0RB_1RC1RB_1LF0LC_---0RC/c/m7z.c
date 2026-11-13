/* m7z MAXEVENTS KEEP [CHECK]: run 1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC from blank; at each fresh left cell in state A
   the tape is A>0 W^K Z (W = 1101101101). If K > KEEP+4, drop K-KEEP copies of W (the sweeps cross W^K uniformly, so
   Z does not see K). Print every CHECK-th event "event K Zlen hash" and look for a repeat of Z with Brent's method. */
#include "../../../tools/c/tm.h"
static const char *W="1101101101";
static unsigned long long zhash(tm_tape*t,long long p){unsigned long long h=1469598103934665603ULL;for(long long q=p;q<=t->hi;q++){h^=tm_get(t,q)+1;h*=1099511628211ULL;}h^=(unsigned long long)(t->hi-p+1)<<1;return h;}
int main(int argc,char**argv){tm_machine m; tm_parse("1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC",&m);
 long long MAXE=atoll(argv[1]); int KEEP=atoi(argv[2]); long long CHECK=argc>3?atoll(argv[3]):0;
 tm_tape t; tm_tape_init(&t,1<<16); int st=0; long long lo0=1, ev=0, totK=0, steps=0;
 unsigned long long saved=0; long long savedEv=-1, power=1, lam=0; long long Ksaved=0;
 while(ev<MAXE){
  if(st==0 && t.head<lo0){ lo0=t.head;
    long long p=t.head+1,K=0; while(p+9<=t.hi){int ok=1;for(int j=0;j<10;j++) if(tm_get(&t,p+j)!=W[j]-'0'){ok=0;break;} if(!ok)break; K++; p+=10;}
    unsigned long long h=zhash(&t,p);
    if(CHECK && ev%CHECK==0) printf("%lld %lld %lld %lld %016llx\n",ev,steps,totK+K,t.hi-p+1,h);
    if(h==saved){ printf("REPEAT event %lld equals event %lld (period %lld events), K then %lld now %lld (total copies %lld)\n",ev,savedEv,ev-savedEv,Ksaved,K,totK+K); fflush(stdout); return 0; }
    if(ev-savedEv==power){ saved=h; savedEv=ev; power*=2; Ksaved=totK+K; }
    if(K>KEEP+4){ long long drop=K-KEEP; long long a=t.head+1, b=a+10*drop; /* move cells [b,hi] to a */
      for(long long q=b;q<=t.hi;q++){ t.c[q-10*drop+t.off]=t.c[q+t.off]; }
      for(long long q=t.hi-10*drop+1;q<=t.hi;q++) t.c[q+t.off]=0;
      t.hi-=10*drop; totK+=drop; }
    ev++; }
  if(!tm_step(&m,&t,&st)){printf("halted after %lld steps\n",steps);return 0;}
  steps++; }
 printf("no repeat in %lld events (%lld steps, total copies %lld)\n",ev,steps,totK);
}
