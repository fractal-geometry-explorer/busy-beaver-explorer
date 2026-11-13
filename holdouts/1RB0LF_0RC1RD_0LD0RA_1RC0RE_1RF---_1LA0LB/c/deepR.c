#include <stdio.h>
#include <stdlib.h>
// mirror of deep.c: min head position per doubling window, and max
int main(int argc,char**argv){
  char*m=argv[1]; long long N=atoll(argv[2]);
  int W[6][2],Mv[6][2],S[6][2];
  for(int i=0;i<6;i++)for(int b=0;b<2;b++){char*t=m+7*i+3*b; if(t[2]=='-'){S[i][b]=-1;continue;} W[i][b]=t[0]-'0';Mv[i][b]=t[1]=='R'?1:-1;S[i][b]=t[2]-'A';}
  int SZ=1<<26; unsigned char*tp=calloc(SZ,1); long p=SZ/2; int s=0; long mx=-(1<<30),mn=1<<30; long long nx=2;
  for(long long n=0;n<N;n++){int b=tp[p]; if(S[s][b]<0){printf("HALT %lld\n",n);fflush(stdout);return 0;} tp[p]=W[s][b]; p+=Mv[s][b]; s=S[s][b]; if(p-SZ/2>mx)mx=p-SZ/2; if(p-SZ/2<mn)mn=p-SZ/2;
    if(n+1==nx){printf("[%lld,%lld) minpos %ld maxpos %ld\n",nx/2,nx,mn,mx); fflush(stdout); nx*=2; mn=1<<30;}}
  printf("no halt in %lld steps\n",N);
}
