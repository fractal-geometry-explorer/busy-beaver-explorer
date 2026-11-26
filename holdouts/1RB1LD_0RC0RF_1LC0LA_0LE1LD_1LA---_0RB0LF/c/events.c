// Events of 1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF from blank tape, by direct simulation.
// "STEP L blocks": the head, in state D, is on the blank cell left of every 1 (blocks of 1s, zK = K zeros between).
// "STEP R blocks gK": the head, in state C, is on a blank cell right of every 1, K blank cells after the last 1.
// usage: events STEPS [FROM_STEP]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<24)
static unsigned char tape[N];
int main(int c,char**v){ long long max=atoll(v[1]); long long from=c>2?atoll(v[2]):0;
  // A0 1RB A1 1LD B0 0RC B1 0RF C0 1LC C1 0LA D0 0LE D1 1LD E0 1LA E1 halt F0 0RB F1 0LF
  static const int W[6][2]={{1,1},{0,0},{1,0},{0,1},{1,-1},{0,0}}; static const int Dr[6][2]={{1,-1},{1,1},{-1,-1},{-1,-1},{-1,0},{1,-1}}; static const int S[6][2]={{1,3},{2,5},{2,0},{4,3},{0,-1},{1,5}};
  long pos=N/2, lo=N/2, hi=N/2-1; int st=0; long long n=0;
  while(n<max){ int b=tape[pos]; if(st==4&&b==1){ printf("%lld HALT\n",n+1); return 0; }
    tape[pos]=W[st][b]; if(tape[pos]){ if(pos<lo)lo=pos; if(pos>hi)hi=pos; } pos+=Dr[st][b]; st=S[st][b]; n++;
    if(st==3 && pos<lo && tape[pos]==0 && n>=from){ printf("%lld L",n); long i=lo; while(i<=hi){ long j=i; while(j<=hi&&tape[j]==tape[i]) j++; if(tape[i]) printf(" %ld",j-i); else printf(" z%ld",j-i); i=j; } printf("\n"); }
    else if(st==2 && pos>hi && tape[pos]==0 && n>=from){ printf("%lld R",n); long i=lo; while(i<=hi){ long j=i; while(j<=hi&&tape[j]==tape[i]) j++; if(tape[i]) printf(" %ld",j-i); else printf(" z%ld",j-i); i=j; } printf(" g%ld\n",pos-hi-1); }
  }
  printf("%lld running\n",n); return 0; }
