// Bit model of 1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA after its transient.
// Word w[0..n), w[0]=0.  One lap: s=X; for j=1..n-1: out=w[j]^inv(s), s=delta(s,w[j]); then append 10 (s=P) or 110 (s=Y); halt if s is X or Q.
// Usage: model LAPS < start word (a line of 0/1).  Prints the smallest gap between the last non-synchronised state and the end of the word.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
enum{X,P,Y,Q};
static const unsigned char D[4][2]={{P,X},{X,Y},{X,Q},{Y,Y}}; static const unsigned char INV[4]={1,1,0,0};
int main(int c,char**v){ long L=atol(v[1]); size_t cap=4*L+1000000; unsigned char*w=malloc(cap); long n=0; int ch;
  while((ch=getchar())=='0'||ch=='1') w[n++]=ch-'0';
  long mingap=1L<<60; long next=1; long lastbad=0; long ny=0;
  for(long t=1;t<=L;t++){ int s=X; long bad=0; long run=0;
    // "bad" = last index at which the state sequence is not yet in the cycle X P X X (four in-cycle states in a row end the search)
    for(long j=1;j<n;j++){ int b=w[j]; w[j]=b^INV[s]; int s2=D[s][b]; if(s2>=Y) bad=j; s=s2; }
    if(s==X||s==Q){ printf("HALT at lap %ld n=%ld state %d\n",t,n,s); return 0; }
    if(s==P){ w[n++]=1; w[n++]=0; } else { w[n++]=1; w[n++]=1; w[n++]=0; ny++; }
    long gap=n-bad; if(gap<mingap) mingap=gap; lastbad=bad;
    if(t==next){ printf("lap %ld n=%ld lastcopy=%ld gap=%ld mingap=%ld ratio=%.4f endY=%ld\n",t,n,lastbad,gap,mingap,(double)lastbad/n,ny); fflush(stdout); next*=2; }
  }
  printf("done laps=%ld n=%ld mingap=%ld endY=%ld\n",L,n,mingap,ny); return 0; }
