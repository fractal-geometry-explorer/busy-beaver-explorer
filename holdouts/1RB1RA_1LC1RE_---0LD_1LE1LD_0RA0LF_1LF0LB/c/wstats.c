// The run of 1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB from blank tape, exactly, with the run of 1s as a number and
// the word W in a ring buffer (only the cells near the foot of the run are ever read again), plus statistics of
// every excursion. It simulates the mirror image (W on the left, the run on the right), which is the table of the
// sibling 1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD started in its state C (py/sibling.py: exact), so "left" here is
// "right" on the machine's own tape. Same lines as `runsim ... D A V 1` (n, W) at every power of two.
//
// usage: wstats VISITS BLOCK
//   every BLOCK visits: the step count at the top of the run, the run n, the length of W, and the deepest excursion
//   and the most cells eaten since the last line; at the end, histograms of depth and of cells eaten per excursion.
// A visit is a crossing of the run by the climbing state (here A, the machine's D): 2n+3 steps, done at once.
// The program stops with "too deep" if an excursion reaches below the ring buffer (it never has), and with HALT if the
// machine halts; n reaching 0 is reported.
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
static void pr128(u128 x){char b[50];int i=49;b[i]=0;if(!x)b[--i]='0';while(x){b[--i]='0'+(int)(x%10);x/=10;}fputs(b+i,stdout);}
#define RB (1L<<24)
#define MASK (RB-1)
static unsigned char t[RB];
#define T(i) t[(i)&MASK]
// mirror image, states renamed: 1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD (A..F = 0..5), started in C on blank tape
static const int Wt[6][2]={{1,1},{0,0},{1,1},{1,1},{-1,0},{1,0}};
static const int Dt[6][2]={{1,1},{-1,1},{-1,-1},{1,-1},{0,1},{1,1}};
static const int St[6][2]={{1,0},{2,5},{3,2},{4,1},{-1,0},{5,3}};
static long hd[4096], he[64], hg[64];
int main(int argc,char**argv){
  if(argc<3){fprintf(stderr,"usage: wstats VISITS BLOCK\n");return 2;}
  long maxv=atol(argv[1]), blk=atol(argv[2]);
  long p=1L<<40, rs=p+1, n=0; int s=2; long v=0; u128 steps=0;
  long lo=p, foot=rs, minp=p, n0=0, bd=0, be=0, gd=0, ge=0;
  for(;;){
    if(p>=rs){
      if(s==0&&p==rs){                       // A at the foot of the run: the next visit
        long ni=n;
        while(rs-1>=lo && T(rs-1)==1){rs--;n++;}   // 1s of W right below the run join it
        v++;
        long dep=foot-minp, e=n0-n;
        hd[dep>4095?4095:dep]++; if(e>=0)he[e>63?63:e]++; else hg[-e>63?63:-e]++;
        if(dep>bd)bd=dep; if(e>be)be=e;
        u128 top=steps+(u128)ni+3;            // A climbs the ni cells of the run, writes the top 1, turns: on the top cell
        steps+=(u128)ni+3+(u128)n;            // ... and C walks back down the n+1 cells
        if(v%blk==0||v==maxv){printf("visit %ld steps ",v);pr128(top);printf(" n=%ld W=%ld maxdepth=%ld maxeat=%ld\n",n+1,rs-lo,bd,be);fflush(stdout);
          if(bd>gd)gd=bd; if(be>ge)ge=be; bd=0; be=0;}
        if(v>=maxv)break;
        n++; n0=n; p=rs-1; s=2; foot=rs; minp=p; continue;
      }
      while(rs<=p){T(rs)=(n>0); if(n>0)n--; else printf("the run is used up at visit %ld\n",v); rs++;}
    }
    if(p<minp){minp=p; if(p<lo)lo=p; if(foot-p>RB/2){printf("too deep\n");return 1;}}
    int b=T(p); if(St[s][b]<0){printf("HALT at visit %ld\n",v);return 0;}
    T(p)=Wt[s][b]; p+=Dt[s][b]; s=St[s][b]; steps++;
  }
  printf("deepest excursion %ld cells below the foot, most cells eaten in one excursion %ld\n",gd,ge);
  printf("depth:");for(int d=0;d<4096;d++)if(hd[d])printf(" %d:%ld",d,hd[d]);printf("\n");
  printf("eaten:");for(int d=0;d<64;d++)if(he[d])printf(" %d:%ld",d,he[d]);printf("\n");
  printf("gained from W (1s below the foot joining the run):");for(int d=0;d<64;d++)if(hg[d])printf(" %d:%ld",d,hg[d]);printf("\n");
  return 0;
}
