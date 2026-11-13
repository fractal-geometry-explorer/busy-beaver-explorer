/* 1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD: from Y(n) (0^inf 1^n 0 B>0) to the next Y(n') or a halt, accelerated */
#include "rle.h"
int main(int argc,char**argv){ ll n0=atoll(argv[1]), n1=atoll(argv[2]), st=argc>3?atoll(argv[3]):1;
 for(ll n=n0;n<=n1;n+=st){ tm t; init(&t,"1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD"); push(&t.L,1,n); push(&t.L,0,1); t.st=1;
  ll moves=0; int done=0;
  while(moves<2000000000LL){ moves++; if(!move(&t)){ printf("%lld HALT %lld\n",n,t.steps); done=1; break; }
    if(t.st==1 && topsym(&t.R)==0 && (t.R.n==0||(t.R.n==1&&t.R.a[0].sym==0))){
      ll b=(t.L.n>=1 && t.L.a[0].sym==0)?1:0;
      if(t.L.n-b==2 && t.L.a[b].sym==1 && t.L.a[b+1].sym==0 && t.L.a[b+1].len==1){ printf("%lld %lld %lld\n",n,t.L.a[b].len,t.steps); done=1; break; } } }
  if(!done) printf("%lld ? \n",n); free(t.L.a); free(t.R.a); } }
