// parts: direct simulation; at the given steps prints the positions >= A of adjacent equal cells, 00 as o and 11 as I.
// In a background of pairs these are the particles: separators (o I o), movers and scars (I or o), Q under the head.
// Feed it the left turns printed by sweeps.c to watch a rebuild bounce by bounce.  usage: ./parts MACHINE t1,t2,... A
// parts M t1,t2,... A : at each given step print positions >= A of adjacent equal cells (00 -> 'o', 11 -> 'I'), and head
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int W[6][2],Mv[6][2],N[6][2];
int main(int c,char**v){
  char*m=v[1]; static long long tg[2000000]; int nt=0; char*p=strtok(v[2],","); while(p){tg[nt++]=atoll(p);p=strtok(0,",");}
  long long A=atoll(v[3]);
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*q=m+s*7+r*3; if(q[2]=='-'){N[s][r]=-1;continue;} W[s][r]=q[0]-'0';Mv[s][r]=q[1]=='R'?1:-1;N[s][r]=q[2]-'A';}
  long long S=1<<28; unsigned char*t=calloc(S,1); long long h=S/2,hi=h; int st=0; int ti=0;
  for(long long k=0;ti<nt;k++){
    while(ti<nt && tg[ti]==k){ printf("%lld %c h=%lld hi=%lld :",k,'A'+st,h-S/2,hi-S/2); for(long long i=S/2+A;i<hi;i++) if(t[i]==t[i+1]) printf(" %lld%c",i-S/2,t[i]?'I':'o'); putchar('\n'); ti++;}
    int r=t[h]; int ns=N[st][r]; if(ns<0){printf("HALT %lld\n",k);return 0;}
    t[h]=W[st][r]; h+=Mv[st][r]; st=ns; if(h>hi)hi=h;
  }
  return 0;}
