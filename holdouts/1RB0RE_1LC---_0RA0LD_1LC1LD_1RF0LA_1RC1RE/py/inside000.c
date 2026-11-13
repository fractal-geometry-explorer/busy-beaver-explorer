// Count the times the rightward state reads 0 0 0 strictly inside the tape (between the outermost 1s).
// usage (from the repo root): gcc -O3 -o /tmp/inside000 holdouts/MACHINE/py/inside000.c && /tmp/inside000 MACHINE STEPS RIGHTSTATE
//   RIGHTSTATE is F for 1RB0RE_1LC---_0RA0LD_1LC1LD_1RF0LA_1RC1RE and A for its twin.
#include <stdio.h>
#include <stdlib.h>
int main(int argc,char**argv){
  char*m=argv[1]; long long S=atoll(argv[2]);
  int w[6][2],d[6][2],n[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*x=m+7*s+3*r; if(x[2]=='-'){n[s][r]=-1;continue;} w[s][r]=x[0]-'0'; d[s][r]=x[1]=='R'?1:-1; n[s][r]=x[2]-'A';}
  int Fs=-1; for(int s=0;s<6;s++){ /* rightward pair state: the state X with X0=1R?, X1=1R? both right */ }
  Fs=argv[3][0]-'A';
  long N=1L<<25; unsigned char*t=calloc(N,1); long p=N/2,L1=p,R1=p; int st=0; long long in=0,out=0;
  for(long long k=0;k<S;k++){
    int x=t[p];
    if(n[st][x]<0){printf("HALT %lld\n",k);return 0;}
    if(st==Fs && !x && !t[p+1] && !t[p+2]){ if(p>L1 && p+2<R1){ in++; if(in<10)printf("inside F000 step %lld pos %ld\n",k,p-N/2);} else out++; }
    int wr=w[st][x]; t[p]=wr;
    if(wr){ if(p<L1)L1=p; if(p>R1)R1=p; }
    p+=d[st][x]; st=n[st][x];
    if(p<4||p>N-4){printf("EDGE %lld\n",k);return 0;}
  }
  printf("done %lld steps: F read 000 inside %lld times, at the ends %lld times; cells between outermost 1s %ld\n",S,in,out,R1-L1+1);
  return 0;
}
