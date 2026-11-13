/* blk MACHINE STATE MAXSTEPS b1,b2,...  : start 0^inf 1^b1 0 1^b2 ... 1^bk STATE>0 0^inf; run until the head is,
   in STATE on a 0, right of all the 1s with a 1 just left of it and the tape a pure block word; print result. */
#include "../../../tools/c/tm.h"
int main(int argc,char**argv){
  tm_machine m; tm_parse(argv[1],&m); int S=argv[2][0]-'A'; long long max=atoll(argv[3]);
  tm_tape t; tm_tape_init(&t,1<<16);
  char*p=argv[4]; long long pos=0; int first=1;
  while(*p){ long long b=strtoll(p,&p,10); if(!first){pos++;} first=0;
    for(long long i=0;i<b;i++){ while(pos+t.off>=t.size-2) tm_grow(&t); t.c[pos+t.off]=1; pos++; }
    if(*p==',')p++; }
  t.lo=0; t.head=pos; t.hi=pos; long long N=pos;
  int st=S; long long k=0;
  while(k<max){
    k++;
    if(!tm_step(&m,&t,&st)){ printf("halt %lld head %lld lo %lld\n",k,t.head,t.lo); return 0; }
    if(st==S && t.head>N && t.head>=t.hi && tm_get(&t,t.head)==0 && tm_get(&t,t.head-1)==1){
      /* pure block check */
      long long a=t.lo; while(a<t.head && tm_get(&t,a)==0) a++;
      int ok=1; for(long long i=a;i<t.head-1;i++) if(tm_get(&t,i)==0&&tm_get(&t,i+1)==0){ok=0;break;}
      if(ok){ printf("ok %lld [",k); long long run=0; int f=1;
        for(long long i=a;i<t.head;i++){ if(tm_get(&t,i)) run++; else { printf(f?"%lld":",%lld",run); f=0; run=0; } }
        printf(f?"%lld":",%lld",run); printf("] lo %lld\n",t.lo); return 0; }
    }
  }
  printf("max %lld\n",k); return 0;
}
