/* zper MACHINE MAX 0 PREFIX: at every increment of the left counter (decoded as in lcnt.c), hash the tape right of the
   counter with the head position and state, and report whether that configuration was seen before (and its period). */
#include "../../../tools/c/tm.h"
/* at each left-counter change (decoded as in lcnt), hash the zone right of the "11" separator (to hi) with head offset/state.
   Report: for each new hash, if seen before, the distance in increments. Print summary per window. */
#define HS (1<<22)
static unsigned long long keys[HS]; static long long when[HS];
int main(int argc,char**argv){ tm_machine m; tm_parse(argv[1],&m); long long b=atoll(argv[2]),W=atoll(argv[3]); int P=atoi(argv[4]); int Wd=110;
 tm_tape t; tm_tape_init(&t,1<<16); int st=0; long long k=0; int dirty=1; unsigned long long lastv=0; int lastb=-1; long long ninc=0; long long lastper=-1, perstart=0;
 while(k<b){ k++; long long h=t.head; if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);return 0;}
   if(h-t.lo < Wd+8) dirty=1;
   if(dirty && t.head-t.lo >= Wd+8){ dirty=0;
     long long p=t.lo; while(tm_get(&t,p)==0) p++; p+=P; unsigned long long v=0; int bb=0;
     while(tm_get(&t,p)==1&&tm_get(&t,p+1)==0&&tm_get(&t,p+3)==0){ v=v*2+tm_get(&t,p+2); bb++; p+=4; }
     if(tm_get(&t,p)==1&&tm_get(&t,p+1)==1 && (lastb<0 || v!=lastv || bb!=lastb)){
       lastv=v; lastb=bb; ninc++;
       unsigned long long hsh=1469598103934665603ULL; for(long long q=p;q<=t.hi;q++){ hsh=(hsh^tm_get(&t,q))*1099511628211ULL; }
       hsh=(hsh^(unsigned long long)(t.head-p))*1099511628211ULL; hsh=(hsh^st)*1099511628211ULL; hsh=(hsh^(unsigned long long)(t.hi-p))*1099511628211ULL;
       unsigned long long i=hsh&(HS-1); while(keys[i] && keys[i]!=hsh) i=(i+1)&(HS-1);
       if(keys[i]==hsh){ long long per=ninc-when[i]; if(per!=lastper){ printf("%lld inc#%lld period %lld (zone width %lld, left digits %d) \n",k,ninc,per,t.hi-p+1,bb); lastper=per; fflush(stdout);} }
       else { if(lastper!=-1){ printf("%lld inc#%lld new zone (aperiodic) width %lld digits %d\n",k,ninc,t.hi-p+1,bb); lastper=-1; fflush(stdout);} keys[i]=hsh; }
       when[i]=ninc; } } }
 printf("done %lld steps, %lld increments, last period %lld\n",k,ninc,lastper); }
