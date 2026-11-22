// events: state A reading 0 at p, with tape[p-3..p-1] in {100,110,010} and tape[p+1..p+4] in {0010,1010}. print right part from p+1 (raw), sampled
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int W[6][2],Mv[6][2],Nx[6][2];
int main(int argc,char**argv){
  char*m=argv[1]; long long from=atoll(argv[2]), to=atoll(argv[3]); long long every=atoll(argv[4]);
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*t=m+7*s+3*r; if(t[2]=='-'){Nx[s][r]=-1;continue;} W[s][r]=t[0]-'0';Mv[s][r]=t[1]=='R'?1:-1;Nx[s][r]=t[2]-'A';}
  long long N=1<<22; unsigned char*tp=calloc(N,1); long long p=N/2,lo=p,hi=p; int st=0; long long k=0; long long last=-1e18;
  while(k<to){int r=tp[p];
    if(k>=from && st==0 && r==0 && k-last>=every){
      int d3=tp[p-3]*4+tp[p-2]*2+tp[p-1]; int m4=tp[p+1]*8+tp[p+2]*4+tp[p+3]*2+tp[p+4];
      if((d3==4||d3==6||d3==2)&&(m4==2||m4==10)){ last=k; printf("%lld %lld ",k,p-N/2); for(long long i=lo;i<p;i++)putchar('0'+tp[i]); printf(" A>0 "); for(long long i=p+1;i<=hi;i++)putchar('0'+tp[i]); putchar('\n'); }
    }
    int nx=Nx[st][r]; if(nx<0){printf("HALT %lld\n",k);return 0;}
    tp[p]=W[st][r]; p+=Mv[st][r]; st=nx; k++; if(p<lo)lo=p; if(p>hi)hi=p;}
}
