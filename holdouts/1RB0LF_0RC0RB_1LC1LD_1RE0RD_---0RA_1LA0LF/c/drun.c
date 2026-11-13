#include <stdio.h>
#include <stdlib.h>
// histogram of D-runs (D reading 1): length of run, and the local tape (window) at the start, by position relative to left end
int main(int argc,char**argv){
  char*m=argv[1]; long long N=atoll(argv[2]); int ex=argc>3?atoi(argv[3]):0;
  int W[6][2],Mv[6][2],S[6][2];
  for(int i=0;i<6;i++)for(int b=0;b<2;b++){char*t=m+7*i+3*b; if(t[2]=='-'){S[i][b]=-1;continue;} W[i][b]=t[0]-'0';Mv[i][b]=t[1]=='R'?1:-1;S[i][b]=t[2]-'A';}
  int SZ=1<<24; unsigned char*tp=calloc(SZ,1); long p=SZ/2; if(ex) tp[p+1]=1; int s=0; long lo=p,hi=p;
  static long long hist[64][2]; 
  for(long long n=0;n<N;n++){int b=tp[p];
    if(s==3&&b==1){ // start of D-run if previous state was C
      // measure run length
      long q=p; int L=0; while(tp[q]==1){q++;L++;}
      // after run: cell q is 0 (D writes 1), E at q+1
      int after=tp[q+1]; printf("drun n=%lld pos=%ld len=%d lo=%ld\n",n,p-SZ/2,L,lo-SZ/2); if(L>63)L=63; hist[L][after]++;
      if(after==0){printf("WOULD... n=%lld\n",n);}
      // skip: let simulation proceed normally
    }
    if(S[s][b]<0){printf("HALT %lld\n",n);return 0;} tp[p]=W[s][b]; p+=Mv[s][b]; s=S[s][b]; if(p<lo)lo=p;}
  for(int i=0;i<64;i++) if(hist[i][0]||hist[i][1]) printf("len %d: next1 %lld next0 %lld\n",i,hist[i][1],hist[i][0]);
}
