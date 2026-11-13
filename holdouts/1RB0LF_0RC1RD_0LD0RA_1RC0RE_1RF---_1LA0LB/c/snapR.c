#include <stdio.h>
#include <stdlib.h>
// dump tape (from leftmost 1 to head) when head reaches new RIGHT record in state S(arg), every K
int main(int argc,char**argv){
  char*m=argv[1]; long long N=atoll(argv[2]); long long every=atoll(argv[3]); int st=argv[4][0]-'A';
  int W[6][2],Mv[6][2],S[6][2];
  for(int i=0;i<6;i++)for(int b=0;b<2;b++){char*t=m+7*i+3*b; if(t[2]=='-'){S[i][b]=-1;continue;} W[i][b]=t[0]-'0';Mv[i][b]=t[1]=='R'?1:-1;S[i][b]=t[2]-'A';}
  int SZ=1<<22; unsigned char*tp=calloc(SZ,1); long p=SZ/2; int s=0; long lo=p,hi=p; long long cnt=0;
  for(long long n=0;n<N;n++){int b=tp[p]; if(S[s][b]<0){printf("HALT %lld\n",n);return 0;} tp[p]=W[s][b]; p+=Mv[s][b]; s=S[s][b]; if(p<lo)lo=p;
    if(p>hi){hi=p; if(s==st){cnt++; if(cnt%every==0){printf("%lld %ld ",n+1,p-SZ/2); long l=lo; while(!tp[l])l++; for(long i=l;i<=p;i++)putchar('0'+tp[i]); putchar('\n');}}}}
}
