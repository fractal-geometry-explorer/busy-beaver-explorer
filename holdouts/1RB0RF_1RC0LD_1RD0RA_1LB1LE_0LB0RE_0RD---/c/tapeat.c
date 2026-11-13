// tapeat MACHINE < steps(sorted ascending): prints "step state headoffset tape" (tape = visited cells lo..hi, head offset from lo)
#include <stdio.h>
#include <stdlib.h>
#define N (1<<25)
unsigned char tape[N];
int nw[6][2],mv[6][2],ns[6][2];
int main(int c,char**v){char*m=v[1];
 for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*t=m+7*s+3*r; if(t[2]=='-'){ns[s][r]=-1;continue;} nw[s][r]=t[0]-'0';mv[s][r]=t[1]=='R'?1:-1;ns[s][r]=t[2]-'A';}
 long long want,k=0;int p=N/2,lo=p,hi=p,st=0;
 while(scanf("%lld",&want)==1){
  while(k<want){int r=tape[p];int t=ns[st][r];if(t<0){printf("HALT %lld\n",k+1);return 0;}tape[p]=nw[st][r];p+=mv[st][r];st=t;k++;if(p<lo)lo=p;if(p>hi)hi=p;}
  int a=lo,b=hi; while(a<p&&tape[a]==0)a++; while(b>p&&tape[b]==0)b--;
  printf("%lld %c %d ",k,'A'+st,p-a);for(int i=a;i<=b;i++)putchar('0'+tape[i]);putchar('\n');fflush(stdout);}
}
