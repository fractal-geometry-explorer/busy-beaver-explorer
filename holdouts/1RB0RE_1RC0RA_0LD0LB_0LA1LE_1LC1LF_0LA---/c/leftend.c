// leftend MACHINE STEPS [FROM [N]]: at each arrival of the head at the leftmost cell (after >=8 cells away), print
// (from step FROM on, at most N lines)
// step state and the tape tokenized: a^k for (10)^k, single 0/1 otherwise, run-length coded.
#include <stdio.h>
#include <stdlib.h>
#define N (1<<27)
unsigned char tape[N];
int main(int argc,char**argv){char*m=argv[1]; long long steps=atoll(argv[2]); long long from=argc>3?atoll(argv[3]):0; long maxl=argc>4?atol(argv[4]):100000000; long nl=0;
 int nw[6][2],mv[6][2],ns[6][2];
 for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*t=m+s*7+r*3; if(t[0]=='-'){ns[s][r]=-1;continue;} nw[s][r]=t[0]-'0'; mv[s][r]=t[1]=='R'?1:-1; ns[s][r]=t[2]-'A';}
 long pos=N/2,lo=pos,hi=pos; int st=0; int armed=1;
 for(long long i=0;i<steps;i++){int r=tape[pos]; int n=ns[st][r]; if(n<0){printf("HALT %lld\n",i+1);return 0;}
  tape[pos]=nw[st][r]; pos+=mv[st][r]; st=n; if(pos<lo)lo=pos; if(pos>hi)hi=pos;
  if(pos-lo>=8) armed=1;
  if(armed && pos==lo){armed=0; if(i+1<from) continue; printf("%lld %c",i+1,'A'+st);
    long p=lo; char last=0; long cnt=0;
    while(p<=hi){ char t; if(p<hi && tape[p]==1 && tape[p+1]==0){t='a';p+=2;} else {t='0'+tape[p];p++;}
      if(t==last) cnt++; else { if(last){ if(cnt>1) printf(" %c^%ld",last,cnt); else printf(" %c",last);} last=t; cnt=1;} }
    if(cnt>1) printf(" %c^%ld",last,cnt); else printf(" %c",last);
    printf("\n"); fflush(stdout); if(++nl>=maxl) return 0;}
 }}
