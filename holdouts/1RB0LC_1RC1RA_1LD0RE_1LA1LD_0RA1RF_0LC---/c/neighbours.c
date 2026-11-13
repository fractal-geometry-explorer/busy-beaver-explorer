// nb M STEPS: all machines that differ from M in one defined transition (or define the halting one): halts?
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int W[6][2],D[6][2],NS[6][2];
static unsigned char*tp; long long N=1LL<<24;
long long run(long long maxs,int start){ memset(tp,0,N); long long p=N/2,t=0; int st=start;
  while(t<maxs){int y=tp[p];int ns=NS[st][y]; if(ns<0) return t; tp[p]=W[st][y]; p+=D[st][y]; st=ns; t++; if(p<2||p>N-2) return -2;} return -1;}
int main(int c,char**v){ const char*m=v[1]; long long maxs=atoll(v[2]); tp=malloc(N);
  for(int s=0;s<6;s++)for(int y=0;y<2;y++){const char*t=m+7*s+3*y; if(t[2]=='-'){NS[s][y]=-1;continue;} W[s][y]=t[0]-'0';D[s][y]=t[1]=='R'?1:-1;NS[s][y]=t[2]-'A';}
  for(int st=0;st<6;st++){ long long r=run(maxs,st); if(r>=0) printf("start %c halts after %lld\n",'A'+st,r); }
  for(int s=0;s<6;s++)for(int y=0;y<2;y++){ if(NS[s][y]<0) continue; int w0=W[s][y],d0=D[s][y],n0=NS[s][y];
    for(int w=0;w<2;w++)for(int d=-1;d<=1;d+=2)for(int n=0;n<6;n++){ if(w==w0&&d==d0&&n==n0)continue; W[s][y]=w;D[s][y]=d;NS[s][y]=n;
      long long r=run(maxs,0); if(r>=0) printf("%c%d=%d%c%c halts after %lld\n",'A'+s,y,w,d>0?'R':'L','A'+n,r); }
    W[s][y]=w0;D[s][y]=d0;NS[s][y]=n0; }
  return 0;}
