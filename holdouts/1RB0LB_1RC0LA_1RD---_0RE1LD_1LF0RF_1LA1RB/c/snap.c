#include "../../../tools/c/tm.h"
/* snap M MAX turns FROM TO | snap M MAX at S L|R K EVERY | snap M MAX every N
   output lines: step state lo hi head tape(raw 0/1 from lo..hi) */
static void raw(tm_tape*t,int st,long long k){printf("%lld %c %lld %lld %lld ",k,'A'+st,t->lo,t->hi,t->head);for(long long p=t->lo;p<=t->hi;p++)putchar('0'+tm_get(t,p));putchar('\n');}
int main(int argc,char**argv){tm_machine m;tm_parse(argv[1],&m);long long max=atoll(argv[2]);
 tm_tape t;tm_tape_init(&t,1<<16);int st=0;long long k=0;
 if(!strcmp(argv[3],"turns")){long long a=atoll(argv[4]),b=atoll(argv[5]);int dir=0;
  while(k<max){long long h=t.head;int s0=st;k++;if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);return 0;}
   int d=t.head>h?1:-1; if(k>=a&&k<=b&&d!=dir)printf("%lld %c %lld %c\n",k-1,'A'+s0,h,d>0?'>':'<');dir=d;if(k>b)break;}
  return 0;}
 if(!strcmp(argv[3],"at")){int S=argv[4][0]=='*'?-1:argv[4][0]-'A',R=argv[5][0]=='R';long long K=atoll(argv[6]),E=atoll(argv[7]),n=0,c=0;
  while(k<max&&n<K){k++;if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);raw(&t,st,k);return 0;}
   if((S<0||st==S)&&t.head==(R?t.hi:t.lo)){if(c++%E==0){raw(&t,st,k);n++;}}}
  return 0;}
 if(!strcmp(argv[3],"every")){long long N=atoll(argv[4]);while(k<max){k++;if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);return 0;}if(k%N==0)raw(&t,st,k);}}
 return 0;}
