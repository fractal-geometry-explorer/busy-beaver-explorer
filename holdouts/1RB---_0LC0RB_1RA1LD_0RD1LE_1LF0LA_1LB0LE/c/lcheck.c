#include "../../../tools/c/tm.h"
/* lcheck MACHINE FROM TO POS STATE: at each turn at POS (rel. lo at FROM) in STATE, read the left counter
   (4-cell blocks left of the head, skipping the block next to it: 0101 = 1, 0001 = 0) and check it goes up by 1. */
int main(int argc,char**argv){tm_machine m; tm_parse(argv[1],&m); long long from=atoll(argv[2]), to=atoll(argv[3]); long long pos=atoll(argv[4]); int S=argv[5][0]-'A';
 tm_tape t; tm_tape_init(&t,1<<20); int st=0; long long k=0; int ld=0; long long base=0; int set=0; long long n=0, ok=0, bad=0; unsigned long long prev=0; int pd=0;
 while(k<to){ long long h0=t.head; k++; if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);break;}
  int d=t.head>h0?1:-1;
  if(k>=from){ if(!set){base=t.lo;set=1;} if(d!=ld && t.head-base==pos && st==S){
    unsigned long long v=0; int i=0; long long p=t.head-4;
    while(p-4>=t.lo && i<62){ int a=tm_get(&t,p-4),b=tm_get(&t,p-3),c=tm_get(&t,p-2),e=tm_get(&t,p-1);
      if(a==0&&b==1&&c==0&&e==1) v|=1ULL<<i; else if(!(a==0&&b==0&&c==0&&e==1)) break; i++; p-=4; }
    if(n>0){ if(v==prev+1 || (pd==i && v==0 && prev==(1ULL<<i)-1)) ok++; else { bad++; if(bad<5) printf("step %lld: %llu -> %llu (%d digits)\n",k,prev,v,i);} }
    prev=v; pd=i; n++; } }
  ld=d; }
 printf("%lld snapshots, %lld steps +1, %lld others, last value %llu with %d digits\n",n,ok,bad,prev,pd);
}
