/* Samples of 1RB1RF_1RC0RB_0RD1LF_1LE1RE_1LA---_1RA0LC for py/ends.py: each time the head is in A at the right end on a 0, print
   "STEP MIN TAPE": MIN is the leftmost head position since the previous sample, relative to the first 1 of TAPE. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
/* M11 events: head in A at right end on 0. print: step minhead_since_last lo hi tape(lo..hi) */
int W[6][2],Mv[6][2],N[6][2];
int main(int c,char**v){
  const char*M="1RB1RF_1RC0RB_0RD1LF_1LE1RE_1LA---_1RA0LC";
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*g=M+7*s+3*b; if(g[0]=='-'){N[s][b]=-1;continue;} W[s][b]=g[0]-'0';Mv[s][b]=g[1]=='R'?1:-1;N[s][b]=g[2]-'A';}
  long long max=atoll(v[1]); int SZ=1<<22; char*t=calloc(SZ,1); long p=SZ/2,lo=p,hi=p,mn=p; int st=0;
  for(long long k=1;k<=max;k++){
    int b=t[p]; int ns=N[st][b]; if(ns<0){printf("HALT %lld\n",k);return 0;}
    t[p]=W[st][b]; p+=Mv[st][b]; st=ns; if(p<lo)lo=p; if(p>hi)hi=p; if(p<mn)mn=p;
    if(st==0&&p==hi&&t[p]==0){ long l=lo; while(l<hi&&!t[l])l++; printf("%lld %ld ",k,mn-l); for(long i=l;i<hi;i++)putchar('0'+t[i]); putchar('\n'); mn=p; }
  }
  return 0;
}
