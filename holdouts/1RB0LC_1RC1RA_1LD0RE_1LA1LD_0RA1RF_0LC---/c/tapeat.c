// tapeat M timesfile : for each time t (ascending) print "t state tape-with-[X]-marker" trimmed to 1s and head
#include <stdio.h>
#include <stdlib.h>
int W_[6][2],D[6][2],NS[6][2];
int main(int argc,char**argv){
  const char*m=argv[1]; FILE*f=fopen(argv[2],"r");
  for(int s=0;s<6;s++)for(int y=0;y<2;y++){const char*t=m+7*s+3*y; if(t[2]=='-'){NS[s][y]=-1;continue;} W_[s][y]=t[0]-'0';D[s][y]=t[1]=='R'?1:-1;NS[s][y]=t[2]-'A';}
  long long N=1LL<<28; unsigned char*tp=calloc(N,1); long long p=N/2,lo=p,hi=p; int st=0; long long t=0,tt;
  while(fscanf(f,"%lld",&tt)==1){
    while(t<tt){ int y=tp[p]; int ns=NS[st][y]; if(ns<0){printf("HALT %lld\n",t);return 0;} tp[p]=W_[st][y]; p+=D[st][y]; st=ns; if(p<lo)lo=p; if(p>hi)hi=p; t++; }
    long long a=lo,b=hi; while(a<p && tp[a]==0) a++; while(b>p && tp[b]==0) b--;
    printf("%lld %c ",t,'A'+st); for(long long i=a;i<=b;i++){ if(i==p) printf("[");  putchar('0'+tp[i]); if(i==p) printf("]"); } printf("\n"); fflush(stdout);
  }
  return 0;
}
