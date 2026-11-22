// route_census.c: how close the run from blank tape comes to the only halting route.
//
// lean/Route.lean (halt_route) proves that a halt three steps later needs state C reading 0 with a 0 on its left and
// a 1 two cells left (C0 -> 1LD, D0 -> 1LE, E1 halts). This counts, in the first N steps, every time C reads a 0,
// and among those the times the cell on its left is also 0, split into "at the left end of the visited tape" (the
// cell beyond is blank, so no halt) and "inside" (where the next cell decides). It also prints the 13-cell
// neighbourhoods of the C0 events with their counts.
//
// usage: route_census N        build: gcc -O2 -o route_census route_census.c
#include <stdio.h>
#include <stdlib.h>
static const int W[6][2]={{1,1},{1,0},{1,1},{1,0},{0,0},{0,1}};
static const int Mv[6][2]={{1,1},{-1,1},{-1,-1},{-1,-1},{1,0},{-1,1}};
static const int Nx[6][2]={{1,0},{2,3},{3,1},{4,5},{0,-1},{1,4}};   // 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE
#define T (1L<<27)
static unsigned char tp[T];
static long long cnt[1<<14];
int main(int argc,char**argv){
  long long n=atoll(argv[1]); long p=T/2,lo=p,hi=p; int s=0; long long c0=0,atend=0,inside=0;
  for(long long t=0;t<n;t++){
    int c=tp[p];
    if(Nx[s][c]<0){ printf("HALT after %lld steps\n",t); return 0; }
    if(s==2&&c==0){ c0++;
      if(tp[p-1]==0){ if(p-1<=lo) atend++; else { inside++; printf("inside: step %lld, cell two left = %d\n",t,tp[p-2]); } }
      int k=0; for(int i=-6;i<=6;i++) k=k*2+tp[p+i]; k=(k&0x1fff)|((p-6<lo)?(1<<13):0); cnt[k]++; }
    tp[p]=W[s][c]; int ns=Nx[s][c]; p+=Mv[s][c]; s=ns;
    if(p<lo) lo=p; if(p>hi) hi=p;
    if(p<1||p>=T-1){ printf("tape full\n"); return 1; }
  }
  printf("%lld steps: C reads 0 %lld times; with 0 on its left %lld times at the left end, %lld times inside\n",n,c0,atend,inside);
  for(int k=0;k<(1<<14);k++) if(cnt[k]){ printf("%12lld %s ",cnt[k],(k>>13)?"near left end":"inside       ");
    for(int i=12;i>=0;i--){ if(i==6) printf("[C>"); printf("%d",(k>>i)&1); if(i==6) printf("]"); } printf("\n"); }
  return 0;
}
