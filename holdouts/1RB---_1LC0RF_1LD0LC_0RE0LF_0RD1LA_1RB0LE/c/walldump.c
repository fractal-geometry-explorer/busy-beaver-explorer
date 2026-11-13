#include "../../../tools/c/tm.h"
/* walldump MACHINE MAXSTEPS S WORD RESTLEN COUNT: print the rest-of-tape cells at events where rest length == RESTLEN */
int main(int argc,char**argv){
  tm_machine m; tm_parse(argv[1],&m); long long max=atoll(argv[2]); int S=argv[3][0]-'A'; const char*w=argv[4]; int P=strlen(w);
  long long RL=atoll(argv[5]), cnt=atoll(argv[6]), from=argc>7?atoll(argv[7]):0;
  tm_tape t; tm_tape_init(&t,1<<20); int st=0;
  for(long long k=1;k<=max&&cnt>0;k++){
    if(!tm_step(&m,&t,&st)){printf("halted %lld\n",k);return 0;}
    if(k>=from&&st==S&&t.head==t.lo){
      long long p=t.lo+1;
      while(p+P-1<=t.hi){ int ok=1; for(int i=0;i<P;i++) if(tm_get(&t,p+i)!=w[i]-'0'){ok=0;break;} if(!ok)break; p+=P; }
      if(t.hi-p+1!=RL) continue;
      printf("%lld ",k); for(long long q=p;q<=t.hi;q++) putchar('0'+tm_get(&t,q)); putchar('\n'); cnt--;
    }
  }
  return 0;
}
