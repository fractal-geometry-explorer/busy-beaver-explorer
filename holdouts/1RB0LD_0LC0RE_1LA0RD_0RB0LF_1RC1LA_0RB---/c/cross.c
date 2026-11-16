/* crossing profile: how many times the head moves from each cell to the next one on the right, in a run from blank tape.
 * usage: gcc -O2 -o cross cross.c && ./cross MACHINE STEPS   (prints "cell count" lines; cell 0 is the start) */
// cross MACHINE STEPS: number of rightward moves across each boundary (p -> p+1) ; prints pos count
#include <stdio.h>
#include <stdlib.h>
int W[6][2],Mv[6][2],Nx[6][2];
int main(int argc,char**argv){
  char*m=argv[1]; long long max=atoll(argv[2]);
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*t=m+7*s+3*r; if(t[0]=='-'){Nx[s][r]=-1;continue;} W[s][r]=t[0]-'0';Mv[s][r]=t[1]=='R'?1:-1;Nx[s][r]=t[2]-'A';}
  int N=1<<16; unsigned char*tp=calloc(N,1); long long *cnt=calloc(N,8); long long p=N/2,lo=p,hi=p; int st=0; long long k=0;
  while(k<max){int r=tp[p];int nx=Nx[st][r];k++; if(nx<0){printf("HALT %lld\n",k);return 0;} tp[p]=W[st][r]; if(Mv[st][r]>0)cnt[p]++; p+=Mv[st][r];st=nx; if(p<lo)lo=p; if(p>hi)hi=p;}
  for(long long q=lo;q<=hi;q++) printf("%lld %lld\n",q-N/2,cnt[q]);
}
