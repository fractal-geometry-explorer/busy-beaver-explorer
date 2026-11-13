/* dump: run a machine N steps from blank tape; print the state, the head offset, the written tape (trimmed) and its
   left offset.  usage: dump MACHINE N   (tape of 2^25 cells, head starts in the middle) */
#include <stdio.h>
#include <stdlib.h>
int nw[6][2],mv[6][2],ns[6][2];
#define N (1<<25)
unsigned char tape[N];
int main(int c,char**v){char*m=v[1];long long max=atoll(v[2]);
 for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*t=m+7*s+3*r; if(t[2]=='-'){ns[s][r]=-1;continue;} nw[s][r]=t[0]-'0';mv[s][r]=t[1]=='R'?1:-1;ns[s][r]=t[2]-'A';}
 long long p=N/2;int st=0;
 for(long long k=0;k<max;k++){int r=tape[p];int t=ns[st][r];if(t<0){printf("HALT %lld\n",k+1);return 0;}tape[p]=nw[st][r];p+=mv[st][r];st=t;}
 long long lo=0,hi=N-1;while(lo<p&&!tape[lo])lo++;while(hi>p&&!tape[hi])hi--;
 printf("%c %lld\n",'A'+st,p-N/2);for(long long i=lo;i<=hi;i++)putchar('0'+tape[i]);printf("\n%lld\n",lo-N/2);}
