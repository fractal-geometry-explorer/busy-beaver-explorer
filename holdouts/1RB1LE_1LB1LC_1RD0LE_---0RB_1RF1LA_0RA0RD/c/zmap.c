#include "rle.h"
/* from Z(a,b) = 0^inf 1^a 0 1^b 0 B>0 to the next Z configuration (any number of blocks) or halt */
static int isZ(tm *t, ll *out, int *k){ if(t->st!=1 || topsym(&t->R)!=0 || !(t->R.n==0||(t->R.n==1&&t->R.a[0].sym==0))) return 0;
  ll b=(t->L.n>=1 && t->L.a[0].sym==0)?1:0; if((t->L.n-b)%2 || t->L.n-b<2) return 0;
  for(ll j=b;j<t->L.n;j++){ run r=t->L.a[j]; if(((j-b)%2==0 && r.sym!=1) || ((j-b)%2==1 && (r.sym!=0||r.len!=1))) return 0; }
  *k=0; for(ll j=b;j<t->L.n;j+=2) out[(*k)++]=t->L.a[j].len; return 1; }
int main(int argc,char**argv){ ll A0=atoll(argv[1]),A1=atoll(argv[2]),B0=atoll(argv[3]),B1=atoll(argv[4]);
 for(ll a=A0;a<=A1;a++) for(ll b=B0;b<=B1;b++){ tm t; init(&t,"1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD");
  push(&t.L,1,a); push(&t.L,0,1); push(&t.L,1,b); push(&t.L,0,1); t.st=1; ll out[64]; int k; int done=0;
  for(ll i=0;i<200000000;i++){ if(!move(&t)){ printf("%lld %lld HALT\n",a,b); done=1; break; }
    if(i>2 && isZ(&t,out,&k)){ printf("%lld %lld ->",a,b); for(int j=0;j<k;j++) printf(" %lld",out[j]); printf("\n"); done=1; break; } }
  if(!done) printf("%lld %lld ?\n",a,b); free(t.L.a); free(t.R.a); } }
