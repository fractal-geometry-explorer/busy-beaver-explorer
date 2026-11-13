#include "../../../tools/c/tm.h"
/* rmap MACHINE STATE b0 b1 ... bm : tape 1^b0 0 1^b1 ... 0 1^bm, head on last cell in STATE; run to the next visit of the
   right end in STATE reading 1 (head==hi), print steps and the blocks.  MAXSTEPS env (default 1e11). */
int main(int argc,char**argv){ tm_machine m; tm_parse(argv[1],&m); int S=argv[2][0]-'A'; long long max=getenv("MAXSTEPS")?atoll(getenv("MAXSTEPS")):100000000000LL;
  tm_tape t; tm_tape_init(&t,1<<22); long long p=0;
  for(int i=3;i<argc;i++){ long long b=atoll(argv[i]); for(long long j=0;j<b;j++){ t.c[p+t.off]=1; p++; } if(i<argc-1){ p++; } }
  t.lo=0; t.hi=p-1; t.head=p-1; int st=S; long long k=0; int away=0;
  while(k<max){ k++; if(!tm_step(&m,&t,&st)){ printf("HALT %lld\n",k); return 0;}
    if(t.head<t.hi-2) away=1;
    if(away && st==S && t.head==t.hi && tm_get(&t,t.head)==1){
      printf("%lld :",k); long long q=t.lo; while(q<=t.hi){ int v=tm_get(&t,q); long long r=q; while(r<=t.hi&&tm_get(&t,r)==v) r++; if(v) printf(" %lld",r-q); else if(r-q>1) printf(" 0^%lld",r-q); q=r;} printf("\n"); return 0; } }
  printf("MAX\n"); return 0; }
