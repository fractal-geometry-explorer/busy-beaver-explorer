/* longrun MACHINE MAX: run from blank tape; at 10^k and 3*10^k steps print the visited range, the ones and how often the halting state has been entered.  gcc -O2 -o longrun longrun.c */
#include <stdio.h>
#include <stdlib.h>
int W[6][2],Mv[6][2],Nx[6][2];
int main(int argc,char**argv){
  char*m=argv[1]; long long max=atoll(argv[2]);
  int hs=-1,hr=-1;
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*t=m+7*s+3*r; if(t[0]=='-'){Nx[s][r]=-1;hs=s;hr=r;continue;} W[s][r]=t[0]-'0';Mv[s][r]=t[1]=='R'?1:-1;Nx[s][r]=t[2]-'A';}
  int N=1<<16; unsigned char*tp=calloc(N,1); long long p=N/2,lo=p,hi=p; int st=0; long long k=0; long long hent=0;
  long long next=10; int third=0;
  while(k<max){
    long long lim = next<max?next:max;
    while(k<lim){int r=tp[p];int nx=Nx[st][r];k++; if(nx<0){printf("HALT %lld\n",k);fflush(stdout);return 0;} tp[p]=W[st][r];p+=Mv[st][r];st=nx; if(st==hs){hent++;} if(p<lo)lo=p; if(p>hi)hi=p;}
    long long ones=0; for(long long q=lo;q<=hi;q++) ones+=tp[q];
    printf("%lld lo=%lld hi=%lld width=%lld ones=%lld halt_state_entries=%lld\n",k,lo-N/2,hi-N/2,hi-lo+1,ones,hent); fflush(stdout);
    if(third){ next=next/3*10; third=0;} else {next*=3; third=1;}
  }
}
