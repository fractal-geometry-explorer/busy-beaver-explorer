/* check_map: run the machine from D at the left end of 10 1^N, for N = N0, N0+STEP, ..., N1, until it is back at
   D at the left end of 10 1^N2 (prints "N N2 steps") or halts (N2 = -2).  Compare with py/orbit.py step().
   usage: gcc -O2 -o check_map check_map.c && ./check_map 8 3000 2 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define NN (1<<22)
int W[6][2],D[6][2],S[6][2];
int main(int argc,char**argv){
  char*m="1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE";
  for(int i=0;i<6;i++) for(int r=0;r<2;r++){ char*g=m+7*i+3*r; if(g[2]<'A'||g[2]>'F'){S[i][r]=-1;continue;} W[i][r]=g[0]-'0'; D[i][r]=g[1]=='R'?1:-1; S[i][r]=g[2]-'A'; }
  int N0=atoi(argv[1]),N1=atoi(argv[2]),stepN=atoi(argv[3]);
  unsigned char*tp=malloc(NN);
  for(int N=N0;N<=N1;N+=stepN){
    memset(tp,0,NN); int p=NN/2; tp[p]=1;tp[p+1]=0; for(int i=0;i<N;i++) tp[p+2+i]=1;
    int lo=p,hi=p+N+1,s=3; long long t=0; int res=-1;
    while(1){
      int r=tp[p]; if(S[s][r]<0){ res=-2; break;}
      tp[p]=W[s][r]; p+=D[s][r]; s=S[s][r]; t++;
      if(p<lo)lo=p; if(p>hi)hi=p;
      if(s==3&&p==lo&&tp[p]==1&&tp[p+1]==0&&t>5){ int ok=1; for(int i=p+2;i<=hi;i++) if(!tp[i]){ok=0;break;} if(ok){res=hi-p-1;break;} }
      if(t>4000000000LL){res=-3;break;}
    }
    printf("%d %d %lld\n",N,res,t);
  }
}
