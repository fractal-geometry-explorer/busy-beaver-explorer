// vdump T0 T1 EVERY: at every EVERY-th visit to the right end (a new rightmost cell after the head was 50+ cells back)
// with step >= T0, up to step T1, print: visit number, step, state, head offset from the left end, leftmost offset
// since the previous visit, then the tape from the left end to the cell before the head.  Used by py/round_check.py.
#include <stdio.h>
#include <stdlib.h>
int W[6][2]={{1,1},{1,0},{1,1},{1,0},{0,9},{0,1}};
int Mv[6][2]={{1,1},{-1,1},{-1,-1},{-1,-1},{1,0},{-1,1}};
int N[6][2]={{1,0},{2,3},{3,1},{4,5},{0,-1},{1,4}};
#define T (1<<28)
unsigned char tp[T];
// at every EVERY-th right visit in [t0,t1], print: visitno t state headcell(=hi) min-since-last-visit, then tape lo..hi-1
int main(int argc,char**argv){
  long long t0=atoll(argv[1]), t1=atoll(argv[2]); int every=atoi(argv[3]);
  long p=T/2,lo=p,hi=p; int s=0; long mn=p; int armed=0; long long nv=0;
  for(long long t=1;t<=t1;t++){
    int c=tp[p]; if(s==4&&c==1){printf("HALT %lld\n",t);return 0;}
    tp[p]=W[s][c]; int ns=N[s][c]; p+=Mv[s][c]; s=ns; if(p<lo)lo=p; if(p<mn)mn=p;
    if(p<hi-50) armed=1;
    if(p>hi){ hi=p; if(armed){ nv++; if(t>=t0 && nv%every==0){ printf("%lld %lld %c %ld %ld ",nv,t,'A'+s,p-lo,mn-lo); for(long i=lo;i<p;i++) putchar('0'+tp[i]); putchar('\n'); } mn=p; armed=0; } }
  }
}
