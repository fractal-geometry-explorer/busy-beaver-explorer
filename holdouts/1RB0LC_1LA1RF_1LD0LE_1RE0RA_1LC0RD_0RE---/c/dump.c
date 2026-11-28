// dump: direct simulation; at each given step prints "k state head lo hi cells[lo..hi]" (positions from the start cell).
// usage: ./dump MACHINE k1,k2,...   (used by py/mover_sim.py check)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int W[6][2],Mv[6][2],N[6][2];
int cmp(const void*a,const void*b){long long x=*(long long*)a,y=*(long long*)b;return x<y?-1:x>y;}
int main(int c,char**v){
  char*m=v[1]; static long long tg[100000]; int nt=0; char*p=strtok(v[2],","); while(p){tg[nt++]=atoll(p);p=strtok(0,",");}
  qsort(tg,nt,sizeof(long long),cmp);
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*q=m+s*7+r*3; if(q[2]=='-'){N[s][r]=-1;continue;} W[s][r]=q[0]-'0';Mv[s][r]=q[1]=='R'?1:-1;N[s][r]=q[2]-'A';}
  long long S=1<<28; unsigned char*t=calloc(S,1); long long h=S/2,lo=h,hi=h; int st=0; int ti=0;
  for(long long k=0;ti<nt;k++){
    while(ti<nt&&tg[ti]==k){ printf("%lld %c %lld %lld %lld ",k,'A'+st,h-S/2,lo-S/2,hi-S/2); for(long long i=lo;i<=hi;i++)putchar('0'+t[i]); putchar('\n'); ti++;}
    if(ti>=nt)break;
    int r=t[h]; int ns=N[st][r]; if(ns<0){printf("HALT %lld\n",k);return 0;}
    t[h]=W[st][r]; h+=Mv[st][r]; st=ns; if(h>hi)hi=h; if(h<lo)lo=h;
  }
  return 0;}
