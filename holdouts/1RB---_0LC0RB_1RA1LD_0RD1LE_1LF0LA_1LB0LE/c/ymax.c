#include "../../../tools/c/tm.h"
/* per interval between left-end extensions: for each state, the max over positions of turns in that state; print the max of A-turns */
#define W 8192
int main(int argc,char**argv){tm_machine m; tm_parse(argv[1],&m); long long n=atoll(argv[2]); int side=argv[3][0];
 tm_tape t; tm_tape_init(&t,1<<20); int st=0; int ld=0; static long long H[W]; long long last=0;
 for(long long k=1;k<=n;k++){ long long lo=t.lo,hi=t.hi,h0=t.head; if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);break;}
  int d=t.head>h0?1:-1; if(d!=ld){ long long p=t.head+W/2; if(p>=0&&p<W) H[p]++; } ld=d;
  if((side=='L'&&t.lo<lo)||(side=='R'&&t.hi>hi)){ if(k-last>1000){ long long mx=0; int pm=0; for(int p=0;p<W;p++) if(H[p]>mx){mx=H[p];pm=p;} printf("%lld width %lld maxturns %lld at %lld\n",k,t.hi-t.lo+1,mx,pm-W/2-t.lo); memset(H,0,sizeof H);} last=k; }
 }
}
