#include "../../../tools/c/tm.h"
/* rcheck MACHINE FROM TO POS STATE OFF1,OFF2,...: at each turn at POS in STATE read the bits at head+OFFi (lowest
   first) and check the number goes up by 1 modulo 2^(number of offsets). */
int main(int argc,char**argv){tm_machine m; tm_parse(argv[1],&m); long long from=atoll(argv[2]), to=atoll(argv[3]); long long pos=atoll(argv[4]); int S=argv[5][0]-'A';
 int off[64],no=0; char*q=argv[6]; while(*q){ off[no++]=atoi(q); while(*q&&*q!=',')q++; if(*q)q++; }
 tm_tape t; tm_tape_init(&t,1<<20); int st=0; long long k=0; int ld=0; long long base=0; int set=0; long long n=0,ok=0,bad=0; unsigned long long prev=0, mask=(no>=64)?~0ULL:((1ULL<<no)-1);
 while(k<to){ long long h0=t.head; k++; if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);break;}
  int d=t.head>h0?1:-1;
  if(k>=from){ if(!set){base=t.lo;set=1;} if(d!=ld && t.head-base==pos && st==S){
    unsigned long long v=0; for(int i=0;i<no;i++) if(tm_get(&t,t.head+off[i])) v|=1ULL<<i;
    if(n>0){ if(v==((prev+1)&mask)) ok++; else { bad++; if(bad<4) printf("step %lld: %llu -> %llu\n",k,prev,v);} }
    prev=v; n++; } }
  ld=d; }
 printf("%lld snapshots, %lld steps +1 (mod 2^%d), %lld others, last %llu\n",n,ok,no,bad,prev);
}
