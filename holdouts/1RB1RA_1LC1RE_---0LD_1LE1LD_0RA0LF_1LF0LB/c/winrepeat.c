// Does the stretch of K cells of W next to the run ever repeat? For 1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB from
// blank tape (simulated as its mirror image, as in wstats.c): at every visit, a 64-bit hash of the K cells next to the
// run, looked up among those of all earlier visits. usage: winrepeat VISITS K
// A repeat with K at least the depth of every excursion in between would make the machine a translated cycler; there
// is none for K = 160 in 2·10^6 visits (for K = 40 almost every visit repeats an earlier one, for K = 80 0.7% do).
// A hash match is only a candidate (it is not compared cell by cell), so "no repeat" is the reliable direction.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define RB (1L<<24)
#define MASK (RB-1)
static unsigned char t[RB];
#define T(i) t[(i)&MASK]
int Wt[6][2]={{1,1},{0,0},{1,1},{1,1},{-1,0},{1,0}};
int Dt[6][2]={{1,1},{-1,1},{-1,-1},{1,-1},{0,1},{1,1}};
int St[6][2]={{1,0},{2,5},{3,2},{4,1},{-1,0},{5,3}};
#define HS (1L<<27)
uint64_t *hk; uint32_t *hv;
int main(int argc,char**argv){
  long maxv=atol(argv[1]); int K=atoi(argv[2]);
  hk=calloc(HS,8); hv=calloc(HS,4);
  long p=1L<<40, rs=p+1, n=0; int s=2; long v=0; long lo=p;
  long found=0;
  for(;;){
    if(p>=rs){
      if(s==0&&p==rs){
        while(rs-1>=lo && T(rs-1)==1){rs--;n++;}
        v++;
        uint64_t h=1469598103934665603ULL; for(long i=rs-K;i<rs;i++){h^=T(i)+1;h*=1099511628211ULL;} h|=1;
        uint64_t idx=(h>>5)&(HS-1);
        while(hk[idx]&&hk[idx]!=h) idx=(idx+1)&(HS-1);
        if(hk[idx]==h){ if(found<10) printf("repeat: visit %ld equals visit %u (K=%d)\n",v,hv[idx],K); found++; }
        else {hk[idx]=h;hv[idx]=v;}
        if(v>=maxv)break;
        n++; p=rs-1; s=2; continue;
      }
      while(rs<=p){T(rs)=(n>0); if(n>0)n--; rs++;}
    }
    if(p<lo)lo=p;
    int b=T(p); if(St[s][b]<0){printf("HALT\n");return 0;}
    T(p)=Wt[s][b]; p+=Dt[s][b]; s=St[s][b];
  }
  printf("K=%d visits %ld repeats %ld\n",K,v,found);
}
