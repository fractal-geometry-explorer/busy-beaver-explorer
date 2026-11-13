// jumps MACHINE STEPS: track arrivals of the head at the left end of the visited region after a visit to the
// right end (full sweeps). Whenever the gap between two such arrivals exceeds 8x the previous gap, print the
// tape at the arrival before the jump and at the arrival after it (raw 0/1 from lo to hi), plus the F-entry count.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<26)
unsigned char tape[N]; char *buf;
int main(int argc,char**argv){
  char*m=argv[1]; long long steps=atoll(argv[2]);
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*t=m+s*7+r*3; if(t[0]=='-'){ns[s][r]=-1;continue;} nw[s][r]=t[0]-'0'; mv[s][r]=t[1]=='R'?1:-1; ns[s][r]=t[2]-'A';}
  long pos=N/2,lo=pos,hi=pos; int st=0,last=0; long long prevL=0,gap=1,f0=0,f1=0; buf=malloc(N); long blen=0;
  for(long long i=0;i<steps;i++){
    int r=tape[pos]; int n=ns[st][r]; if(n<0){printf("HALT %lld\n",i);return 0;}
    if(st==5){ if(r)f1++; else f0++; }
    tape[pos]=nw[st][r]; pos+=mv[st][r]; st=n;
    if(pos<lo)lo=pos; if(pos>hi)hi=pos;
    if(pos<=2||pos>=N-2){printf("OUT\n");return 0;}
    int side=0; if(pos==lo)side=-1; else if(pos==hi)side=1;
    if(side&&side!=last){ last=side;
      if(side<0){ long long g=i+1-prevL;
        if(g>8*gap && prevL>0){ printf("PRE %s\n",buf); printf("POST %lld %c %ld f0=%lld f1=%lld ",i+1,'A'+st,hi-lo+1,f0,f1); for(long p=lo;p<=hi;p++)putchar('0'+tape[p]); putchar('\n'); fflush(stdout);}
        gap=g; prevL=i+1;
        blen=sprintf(buf,"%lld %c %ld ",i+1,'A'+st,hi-lo+1); for(long p=lo;p<=hi;p++)buf[blen++]='0'+tape[p]; buf[blen]=0; }
    }
  }
  printf("END f0=%lld f1=%lld width=%ld\n",f0,f1,hi-lo+1);
  return 0;}
