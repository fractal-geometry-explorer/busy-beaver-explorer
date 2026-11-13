#include <stdio.h>
#include <stdlib.h>
/* Runs of zeros in 1RB1LF_1RC0RA_0RD1RA_1RE1LA_0LA---_1RF0LD.  A run of zeros grows for good only when F, having
   just moved right from F reading 0, reads a 1: that 1 is cleared and joins the r zeros on its right (the step
   follows B reading 1 1 0^r).  Counts r for interior runs (a 1 beyond) and edge runs (blank beyond).
   usage: zeroruns STEPS */
int main(int argc,char**argv){
  const char*m="1RB1LF_1RC0RA_0RD1RA_1RE1LA_0LA---_1RF0LD"; long long N=atoll(argv[1]);
  int W[6][2],Dd[6][2],S[6][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*x=m+s*7+b*3; if(x[2]=='-'){S[s][b]=-1;continue;} W[s][b]=x[0]-'0';Dd[s][b]=x[1]=='R'?1:-1;S[s][b]=x[2]-'A';}
  long L=1<<26; unsigned char*t=calloc(L,1); long p=L/2,lo=p,hi=p; int s=0,ps=-1,pb=-1;
  long long cnt[16]={0},cntb[16]={0}; int shown[16]={0};
  for(long long n=0;n<N;n++){
    int b=t[p]; int ns=S[s][b]; if(ns<0){printf("HALT %lld\n",n);break;}
    if(s==5&&b==1&&ps==5&&pb==0){ long c=p; while(c<hi&&t[c+1]==0)c++; int r=c-p; int interior=(c<hi); if(r>15)r=15; if(interior)cnt[r]++; else cntb[r]++;
      if(r>=2&&shown[r]<5){shown[r]++;printf("r=%d int=%d n=%lld: ",r,interior,n); for(long i=p-30;i<=p+20;i++)putchar(i==p?'*':'0'+t[i]); putchar('\n');}}
    ps=s;pb=b;
    t[p]=W[s][b]; p+=Dd[s][b]; s=ns; if(p<lo)lo=p; if(p>hi)hi=p;
  }
  for(int r=0;r<16;r++)if(cnt[r]||cntb[r])printf("r %d: interior %lld edge %lld\n",r,cnt[r],cntb[r]);
}
