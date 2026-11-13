/* 1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD: the Y(n) = 0^inf 1^n 0 B>0 0^inf visits of the run from blank tape, on the accelerated RLE simulator */
#include "rle.h"
int main(int argc,char**argv){ tm t; init(&t,"1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD"); ll maxmoves=atoll(argv[1]);
  ll prev=-1;
  for(ll i=0;i<maxmoves;i++){ if(!move(&t)){ printf("HALT at step %lld\n",t.steps); print_tape(&t,stdout); return 0; }
    if(t.st==1 && topsym(&t.R)==0){
      /* R blank? */
      int rb = t.R.n==0 || (t.R.n==1 && t.R.a[0].sym==0);
      if(!rb) continue;
      /* L = [1^n, 0] possibly with 0-run at bottom */
      ll b=0; if(t.L.n>=1 && t.L.a[0].sym==0) b=1;
      if(t.L.n-b==2 && t.L.a[b].sym==1 && t.L.a[b+1].sym==0 && t.L.a[b+1].len==1){
        ll n=t.L.a[b].len; if(n!=prev){ printf("%lld Y %lld\n",t.steps,n); fflush(stdout); prev=n; } }
    }
  }
  printf("stopped at step %lld\n",t.steps); }
