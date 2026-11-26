// Laps of 1RB0LD_1RC0RD_1LA0RC_1RE1LB_1LF0LA_---0LE. A lap ends when the head reaches a new leftmost cell after more
// than 200 steps away from it. Per lap prints: lap, step, leftmost cell, turning point (rightmost cell of the lap),
// rightmost cell so far (cells relative to the start). usage: gcc -O2 -o laps laps.c && ./laps STEPS
#include <stdio.h>
#include <stdlib.h>
#define T 4000000
static unsigned char tape[T];
int main(int argc,char**argv){
  char *m="1RB0LD_1RC0RD_1LA0RC_1RE1LB_1LF0LA_---0LE"; long N=atol(argv[1]);
  int w[6][2],d[6][2],n[6][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*x=m+7*s+3*b; if(x[0]=='-'){n[s][b]=-1;continue;} w[s][b]=x[0]-'0'; d[s][b]=x[1]=='R'?1:-1; n[s][b]=x[2]-'A';}
  long p=T/2,lo=p,hi=p,mx=p,last=0; int s=0; long cyc=0;
  for(long i=0;i<N;i++){int b=tape[p]; if(n[s][b]<0){printf("HALT %ld\n",i);return 0;} tape[p]=w[s][b]; p+=d[s][b]; s=n[s][b];
    if(p>mx)mx=p; if(p>hi)hi=p;
    if(p<lo){ if(i-last>200){ printf("%ld %ld %ld %ld %ld\n",cyc,i,lo-T/2,mx-T/2,hi-T/2); cyc++; mx=p;} lo=p; last=i;}
  }
}
