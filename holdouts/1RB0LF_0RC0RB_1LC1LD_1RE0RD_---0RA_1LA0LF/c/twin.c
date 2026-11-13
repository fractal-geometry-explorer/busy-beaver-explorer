#include <stdio.h>
#include <stdlib.h>
#include <string.h>
// Run M19 from blank and from (blank + 1 at cell +1) [= M27 after its first step, mirrored].
// At each new-left-record F event of each run (k-th of each), compare: tape27 == tape19 + extra '1' at the right end.
typedef struct {unsigned char*tp; long p,lo,hi; int s; long long n;} R;
int W[6][2],Mv[6][2],S[6][2]; int SZ=1<<23;
// advance r until next new-left-record in state F; return 0 on halt
int adv(R*r){ for(;;){int b=r->tp[r->p]; if(S[r->s][b]<0) return 0; r->tp[r->p]=W[r->s][b]; r->p+=Mv[r->s][b]; r->s=S[r->s][b]; r->n++; if(r->p>r->hi) r->hi=r->p; if(r->p<r->lo){r->lo=r->p; if(r->s==5) return 1;}}}
int main(int argc,char**argv){
  char*m="1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF"; long long N=atoll(argv[1]);
  for(int i=0;i<6;i++)for(int b=0;b<2;b++){char*t=m+7*i+3*b; if(t[2]=='-'){S[i][b]=-1;continue;} W[i][b]=t[0]-'0';Mv[i][b]=t[1]=='R'?1:-1;S[i][b]=t[2]-'A';}
  R a={calloc(SZ,1),SZ/2,SZ/2,SZ/2,0,0}, b={calloc(SZ,1),SZ/2,SZ/2,SZ/2,0,0}; b.tp[SZ/2+1]=1; b.hi=SZ/2+1;
  long long ev=0, maxdiff=0;
  while(a.n<N){ if(!adv(&a)||!adv(&b)){printf("halt a.n=%lld b.n=%lld\n",a.n,b.n);return 0;} ev++;
    if(a.p!=b.p){printf("pos differ at event %lld\n",ev);return 1;}
    long ha=a.hi; while(!a.tp[ha])ha--; long hb=b.hi; while(!b.tp[hb])hb--;
    if(hb!=ha+1 || b.tp[hb]!=1 || memcmp(a.tp+a.p,b.tp+b.p,ha-a.p+1)!=0){printf("MISMATCH at event %lld step %lld\n",ev,a.n);return 1;}
    if(b.n-a.n!=maxdiff){maxdiff=b.n-a.n; printf("diff %lld at event %lld step %lld\n",maxdiff,ev,a.n);}
    if((ev&(ev-1))==0) printf("event %lld: steps %lld vs %lld, width %ld, right end %ld\n",ev,a.n,b.n,ha-a.p+1,ha-SZ/2);
  }
  printf("OK: %lld events, M19 steps %lld, twin steps %lld (+1 for M27's first step)\n",ev,a.n,b.n);
}
