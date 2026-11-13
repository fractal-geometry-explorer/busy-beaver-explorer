// yper M steps P: per period between left-end extensions, the cells (rel. to P) whose value differs between consecutive events (A at P), with counts
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<22)
unsigned char tape[N], prev[N]; long long cnt[N];
int main(int argc,char**argv){
  char*m=argv[1]; long long mx=atoll(argv[2]); long P=atol(argv[3]);
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*p=m+s*7+r*3; if(p[2]=='-'){ns[s][r]=-1;continue;} nw[s][r]=p[0]-'0'; mv[s][r]=p[1]=='R'?1:-1; ns[s][r]=p[2]-'A';}
  long pos=N/2,lo=pos,hi=pos; int st=0; long long t=0,ev=0,ev0=0; int have=0;
  while(t<mx){int r=tape[pos]; int s2=ns[st][r]; if(s2<0){printf("HALT %lld\n",t+1);return 0;}
    if(st==0 && pos==N/2+P){ ev++;
      if(have){ for(long i=N/2+P;i<=hi;i++) if(tape[i]!=prev[i]) cnt[i]++; }
      memcpy(prev+N/2+P,tape+N/2+P,hi-(N/2+P)+1); have=1; }
    tape[pos]=nw[st][r]; pos+=mv[st][r]; st=s2; t++;
    if(pos>hi)hi=pos;
    if(pos<lo){ lo=pos; if(ev-ev0>1000){ printf("period events %lld-%lld t=%lld :",ev0,ev,t); long last=-1; for(long i=N/2+P+1;i<=hi;i++) if(cnt[i]>2){ printf(" %ld",i-N/2-P); } printf("\n"); fflush(stdout);} memset(cnt+N/2+P,0,sizeof(long long)*(hi-N/2-P+1)); have=0; ev0=ev; }
  }
}
