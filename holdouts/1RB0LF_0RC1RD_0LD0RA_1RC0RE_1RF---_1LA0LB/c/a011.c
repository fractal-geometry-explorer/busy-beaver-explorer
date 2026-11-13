#include <stdio.h>
#include <stdlib.h>
// M20: count A reading 0 followed by 1 1 (on the right); print positions/time
int main(int argc,char**argv){
  char*m=argv[1]; long long N=atoll(argv[2]);
  int W[6][2],Mv[6][2],S[6][2];
  for(int i=0;i<6;i++)for(int b=0;b<2;b++){char*t=m+7*i+3*b; if(t[2]=='-'){S[i][b]=-1;continue;} W[i][b]=t[0]-'0';Mv[i][b]=t[1]=='R'?1:-1;S[i][b]=t[2]-'A';}
  int SZ=1<<24; unsigned char*tp=calloc(SZ,1); long p=SZ/2; int s=0; long hi=p; long long cnt=0; static long long hist[10000];
  for(long long n=0;n<N;n++){int b=tp[p];
    if(s==0&&b==0&&tp[p+1]&&tp[p+2]){cnt++; hist[p-SZ/2+100<0?0:(p-SZ/2+100>9999?9999:p-SZ/2+100)]++; if(cnt<=3 || (cnt&(cnt-1))==0) printf("n=%lld pos=%ld hi=%ld next=%d\n",n,p-SZ/2,hi-SZ/2,tp[p+3]);}
    if(S[s][b]<0){printf("HALT %lld\n",n);return 0;} tp[p]=W[s][b]; p+=Mv[s][b]; s=S[s][b]; if(p>hi)hi=p;}
  printf("count %lld\n",cnt); for(int i=0;i<10000;i++) if(hist[i]) printf("pos %d: %lld\n",i-100,hist[i]);
}
