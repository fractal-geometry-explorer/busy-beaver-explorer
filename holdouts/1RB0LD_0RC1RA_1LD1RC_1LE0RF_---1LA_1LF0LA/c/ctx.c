/* ctx M N STATE SYM W: tape windows [head-W, head+W] each time STATE reads SYM in the first N steps.
   Cells outside the visited extent print as '.'. Prints distinct windows with counts. */
#include "../../../tools/c/tm.h"
#define HS (1<<20)
static unsigned long long key[HS]; static long long cnt[HS]; static long long first[HS];
int main(int argc,char**argv){tm_machine m; tm_parse(argv[1],&m); long long N=atoll(argv[2]);
 int S=argv[3][0]-'A', Y=atoi(argv[4]), W=atoi(argv[5]);
 tm_tape t; tm_tape_init(&t,1<<16); int st=0;
 for(long long k=0;k<N;k++){ int y=tm_get(&t,t.head);
  if(st==S&&y==Y){ unsigned long long h=1; for(long long p=t.head-W;p<=t.head+W;p++){int v=(p<t.lo||p>t.hi)?2:tm_get(&t,p); h=h*3+v;}
   unsigned long long i=(h*0x9E3779B97F4A7C15ULL)>>44; while(key[i]&&key[i]!=h) i=(i+1)&(HS-1);
   if(!key[i]){key[i]=h;first[i]=k;} cnt[i]++; }
  if(!tm_step(&m,&t,&st)){printf("halted at %lld\n",k+1);break;} }
 for(long long i=0;i<HS;i++) if(key[i]){ unsigned long long h=key[i]; char b[64]; int n=2*W+1;
   for(int j=n-1;j>=0;j--){int v=h%3;h/=3;b[j]=v==2?'.':'0'+v;} b[n]=0;
   printf("%12lld first %12lld  ",cnt[i],first[i]); for(int j=0;j<n;j++){ if(j==W)printf("[%c>%c] ",'A'+S,b[j]); else printf("%c ",b[j]);} printf("\n"); }
}
