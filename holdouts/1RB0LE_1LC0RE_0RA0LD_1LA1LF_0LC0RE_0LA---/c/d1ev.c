/* d1ev MACHINE MAX STATE SYM K: the tape each time the transition (STATE, SYM) fires, at most K lines (the head cell in brackets).  gcc -O2 -o d1ev d1ev.c */
#include <stdio.h>
#include <stdlib.h>
int W[6][2],Mv[6][2],Nx[6][2];
int main(int argc,char**argv){
  char*m=argv[1]; long long max=atoll(argv[2]); int S=argv[3][0]-'A', Y=atoi(argv[4]); long long ml=atoll(argv[5]);
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*t=m+7*s+3*r; if(t[0]=='-'){Nx[s][r]=-1;continue;} W[s][r]=t[0]-'0';Mv[s][r]=t[1]=='R'?1:-1;Nx[s][r]=t[2]-'A';}
  int N=1<<16; unsigned char*tp=calloc(N,1); long long p=N/2,lo=p,hi=p; int st=0; long long k=0,lines=0;
  while(k<max&&lines<ml){int r=tp[p];
    if(st==S&&r==Y){ lines++; printf("%lld %lld ",k,p-N/2); for(long long q=lo;q<=hi;q++){ if(q==p) putchar('['); putchar('0'+tp[q]); if(q==p)putchar(']');} putchar('\n'); }
    int nx=Nx[st][r];k++; if(nx<0){printf("HALT %lld\n",k);break;} tp[p]=W[st][r];p+=Mv[st][r];st=nx; if(p<lo)lo=p; if(p>hi)hi=p;}
}
