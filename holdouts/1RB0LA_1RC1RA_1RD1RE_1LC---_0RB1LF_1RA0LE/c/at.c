/* at.c: print the run-length tape each time the head is in state S reading X (every EVERY-th time, from step FROM). usage: at MACHINE STEPS S X [EVERY [FROM]].  Shared by the G11 batch-4 folders. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
// print RLE tape whenever head in state S reads symbol X (and optionally only every Nth)
int N=1<<22; unsigned char*t; long h,lo,hi; int st;
void rle(long a,long b){ long i=a; while(i<=b){ long j=i; while(j<=b&&t[j]==t[i]) j++; if(j-i==1) printf("%d ",t[i]); else printf("%d^%ld ",t[i],j-i); i=j;} }
int main(int c,char**v){char*M=v[1];long long T=atoll(v[2]); int S=v[3][0]-'A'; int X=atoi(v[4]); long long every=c>5?atoll(v[5]):1; long long T0=c>6?atoll(v[6]):0;
 int w[6][2],mv[6][2],nx[6][2];
 for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*p=M+7*s+3*r; if(p[2]=='-'){nx[s][r]=-1;continue;} w[s][r]=p[0]-'0';mv[s][r]=p[1]=='R'?1:-1;nx[s][r]=p[2]-'A';}
 t=calloc(N,1); h=N/2;lo=h;hi=h; st=0; long long cnt=0;
 for(long long k=1;k<=T;k++){int r=t[h];
  if(st==S && r==X && k>=T0){ if(cnt++%every==0){ printf("%lld: ",k); rle(lo,h-1); printf("%c> ",'A'+st); rle(h,hi); printf("\n");} }
  int s2=nx[st][r]; if(s2<0){printf("halt %lld\n",k);return 0;}
  t[h]=w[st][r]; h+=mv[st][r]; st=s2; if(h>hi)hi=h; if(h<lo)lo=h;
 }}
