#include <stdio.h>
#include <stdlib.h>
// usage: dumpT MACHINE T1 [T2 ...]: tape at exact steps T1<T2<...: t pos state lo hi bits(lo..hi)
int main(int c,char**v){
  char*m=v[1];
  int W[6][2],D[6][2],S[6][2];
  for(int s=0;s<6;s++)for(int y=0;y<2;y++){char*g=m+7*s+3*y; if(g[2]=='-'){S[s][y]=-1;continue;} W[s][y]=g[0]-'0';D[s][y]=g[1]=='R'?1:-1;S[s][y]=g[2]-'A';}
  long SZ=1L<<26; unsigned char*t=calloc(SZ,1); long O=SZ/2,p=O,lo=O,hi=O; int q=0; long long i=0;
  for(int a=2;a<c;a++){ long long T=atoll(v[a]);
    for(;i<T;i++){ int y=t[p]; int ns=S[q][y]; if(ns<0){printf("HALT %lld\n",i+1);return 0;}
      t[p]=W[q][y]; p+=D[q][y]; q=ns; if(p<lo)lo=p; if(p>hi)hi=p; }
    printf("%lld %ld %c %ld %ld ",i,p-O,'A'+q,lo-O,hi-O); for(long j=lo;j<=hi;j++)putchar('0'+t[j]); putchar('\n'); fflush(stdout);
  }
  return 0;
}
