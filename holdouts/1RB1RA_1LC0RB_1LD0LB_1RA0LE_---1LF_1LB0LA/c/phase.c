// One phase of 1RB1RA_1LC0RB_1LD0LB_1RA0LE_---1LF_1LB0LA, cell by cell.
// stdin: lines "P z" (P the tape left of the zero block as a 0/1 string, z the zero block); the head starts on the
// blank cell after 0^z in state B.  Runs to the next phase start (head at the right end in B with >= 7 zeros behind
// it) and prints "P2 z2 left_growth steps", or "HALT steps pos".
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static const int W[6][2]={{1,1},{1,0},{1,0},{1,0},{-1,1},{1,0}};
static const int Mv[6][2]={{1,1},{-1,1},{-1,-1},{1,-1},{0,-1},{-1,-1}};
static const int Q[6][2]={{1,0},{2,1},{3,1},{0,4},{-1,5},{1,0}};
int main(){
  static char buf[1<<22];
  long z;
  while (scanf("%s %ld", buf, &z)==2){
    long n=strlen(buf); long cap=n+z+1000000; long base=500000;
    char *t=calloc(cap+base,1); char *tp=t+base;
    for(long i=0;i<n;i++) tp[i]=buf[i]-'0';
    long len=n+z+1, head=len-1, lo=0; int q=1; long steps=0;
    while(1){
      if(head<lo) lo=head;
      if(head>=len) len=head+1;
      int s=tp[head];
      if(Q[q][s]<0){ printf("HALT %ld %ld\n", steps, head); fflush(stdout); break;}
      int w=W[q][s], mv=Mv[q][s]; tp[head]=w; q=Q[q][s]; head+=mv; steps++;
      if(head==len && q==1 && steps>10){
        long j=len-1; while(j>=lo && tp[j]==0) j--;
        long tz=len-1-j;
        if(tz>=7){
          for(long i=lo;i<=j;i++) putchar('0'+tp[i]);
          printf(" %ld %ld %ld\n", tz, -lo, steps); fflush(stdout); break;
        }
      }
    }
    free(t);
  }
}
