// One left-end visit of 1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF from a given block list, by direct simulation.
// stdin: lines of block lengths (single 0s between the blocks, the head in state D on the blank cell left of the first).
// stdout, one line each: the next left-end event "L b1 zK b2 ... dK" (dK: K blank cells between head and first 1),
// or "HALT n" or "LIMIT".  usage: onestep MAXSTEPS [R]   (R: stop at right-end events too)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<22)
static unsigned char tape[N];
int main(int c,char**v){ long long max=atoll(v[1]); int stopR=c>2;
  static const int W[6][2]={{1,1},{0,0},{1,0},{0,1},{1,-1},{0,0}}; static const int Dr[6][2]={{1,-1},{1,1},{-1,-1},{-1,-1},{-1,0},{1,-1}}; static const int S[6][2]={{1,3},{2,5},{2,0},{4,3},{0,-1},{1,5}};
  char line[1<<16];
  while(fgets(line,sizeof line,stdin)){ memset(tape,0,N); long p=N/2+1; char*q=line; long b; int k;
    long lo=p, hi=p;
    while(sscanf(q,"%ld%n",&b,&k)==1){ q+=k; for(long i=0;i<b;i++) tape[p++]=1; hi=p-1; p++; }
    long pos=N/2; int st=3; long long n=0; int done=0;
    while(n<max){ int bb=tape[pos]; if(st==4&&bb==1){ printf("HALT %lld\n",n+1); done=1; break; }
      tape[pos]=W[st][bb]; if(tape[pos]){ if(pos<lo)lo=pos; if(pos>hi)hi=pos; } pos+=Dr[st][bb]; st=S[st][bb]; n++;
      while(lo<hi && !tape[lo]) lo++;
      while(hi>lo && !tape[hi]) hi--;
      int L=(st==3 && pos<lo && tape[pos]==0), R=(stopR && st==2 && pos>hi && tape[pos]==0);
      if(L||R){ printf(L?"L":"R"); long i=lo; while(i<=hi){ long j=i; while(j<=hi&&tape[j]==tape[i]) j++; if(tape[i]) printf(" %ld",j-i); else printf(" z%ld",j-i); i=j; } if(R) printf(" g%ld",pos-hi-1); else printf(" d%ld",lo-pos-1); printf("\n"); done=1; break; }
    }
    if(!done) printf("LIMIT\n");
  }
  return 0; }
