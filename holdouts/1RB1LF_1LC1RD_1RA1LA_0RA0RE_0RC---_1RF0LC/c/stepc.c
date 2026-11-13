#include "../../../tools/c/tm.h"
/* m4stepc W N : from  W A> 0 (110)^N 1  run to the next such configuration; print "W' N' steps" or "HALT steps" */
static void tm_set(tm_tape*t,long long p,int v){t->c[p+t->off]=(unsigned char)v;}
int main(int argc,char**argv){
  tm_machine m; tm_parse("1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC",&m);
  const char*W=argv[1]; long long N=atoll(argv[2]);
  long long len=strlen(W)+1+3*N+1;
  tm_tape t; tm_tape_init(&t,4*len+1024);
  long long base=0;
  long long p=0;
  for(const char*c=W;*c;c++){ tm_set(&t,base+p,*c-'0'); p++; }
  long long hp=base+p; tm_set(&t,base+p,0); p++;
  for(long long i=0;i<N;i++){tm_set(&t,base+p,1);tm_set(&t,base+p+1,1);tm_set(&t,base+p+2,0);p+=3;}
  tm_set(&t,base+p,1);
  t.lo=base; t.hi=base+p; t.head=hp; int st=0; long long k=0;
  while(1){ k++; if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);return 0;}
    if(st!=0) continue;
    long long q=t.head;
    if(tm_get(&t,q)!=0||tm_get(&t,q-1)!=1||tm_get(&t,q+1)!=1) continue;
    long long r=q+1,n=0;
    while(r+2<=t.hi&&tm_get(&t,r)==1&&tm_get(&t,r+1)==1&&tm_get(&t,r+2)==0){r+=3;n++;}
    if(r!=t.hi||tm_get(&t,r)!=1||n<3) continue;
    for(long long i=t.lo;i<q;i++) putchar('0'+tm_get(&t,i));
    printf(" %lld %lld\n",n,k); return 0;
  }
}
