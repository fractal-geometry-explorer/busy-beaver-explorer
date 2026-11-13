// ev M maxsteps P S [every] [from]: print "count step lo tape" (head marked by |) each time the head is on cell P (from the start cell) in state S
#include <stdio.h>
#include <stdlib.h>
#define N (1<<22)
unsigned char tape[N];
int main(int argc,char**argv){
  char*m=argv[1]; long long mx=atoll(argv[2]); long P=atol(argv[3]); char S=argv[4][0]; long long every=argc>5?atoll(argv[5]):1; long long from=argc>6?atoll(argv[6]):0;
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*p=m+s*7+r*3; if(p[2]=='-'){ns[s][r]=-1;continue;} nw[s][r]=p[0]-'0'; mv[s][r]=p[1]=='R'?1:-1; ns[s][r]=p[2]-'A';}
  long pos=N/2,lo=pos,hi=pos; int st=0; long long t=0,cnt=0;
  while(t<mx){int r=tape[pos]; int s2=ns[st][r]; if(s2<0){printf("HALT %lld\n",t+1);return 0;}
    if(pos-N/2==P && 'A'+st==S){ cnt++; if(t>=from && cnt%every==0){printf("%lld %lld %ld ",cnt,t,lo-N/2); for(long i=lo;i<=hi;i++){ if(i==pos)putchar('|');putchar('0'+tape[i]);} putchar('\n');}}
    tape[pos]=nw[st][r]; 
    pos+=mv[st][r]; st=s2; t++;
    if(pos<lo)lo=pos; if(pos>hi)hi=pos;
  }
}
