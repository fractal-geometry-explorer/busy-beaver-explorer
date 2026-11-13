/* print right part abs 0..hi at D-reads-0-at-1 events immediately before and after each left growth (lo decreases) */
#include "../../../tools/c/tm.h"
int main(int argc,char**argv){
  tm_machine m; tm_parse(argv[1],&m); long long max=atoll(argv[2]);
  tm_tape t; tm_tape_init(&t,1<<16); int st=0; long long k=0,ev=0; int after=0; static char last[1<<16];
  while(k<max){ long long lo=t.lo; k++;
    if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);break;}
    if(t.lo<lo){ printf("B %lld %lld %s\n",ev,k,last); after=1; }
    if(st==3 && t.head==1 && tm_get(&t,1)==0 && tm_get(&t,0)==1 ){ ev++;
      long long n=0; for(long long p=0;p<=t.hi;p++) last[n++]='0'+tm_get(&t,p); last[n]=0;
      if(after){ printf("A %lld %lld %s\n",ev,k,last); after=0; }
    }
  }
}
