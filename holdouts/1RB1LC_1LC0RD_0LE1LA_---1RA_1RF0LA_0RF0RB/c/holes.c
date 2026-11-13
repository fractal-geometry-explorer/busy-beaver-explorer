// holes MACHINE STEPS T0: print the run-length tape at each reversal of the head next to a "00" hole (at least 20 steps apart), after step T0. Feed to a grep for "0^2 A> 0" to see the sweeps of this machine.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<26)
int W[6][2],D[6][2],S[6][2];
unsigned char *tp;
void pr(long long t,int lo,int hi,int p,int s){
  printf("%lld ",t);
  int i=lo;
  while(i<=hi){ if(i==p) printf("%c> ","ABCDEF"[s]); int j=i; while(j<=hi && tp[j]==tp[i] && !(j>i && j==p)) j++; if(j-i==1) printf("%d ",tp[i]); else printf("%d^%d ",tp[i],j-i); i=j; }
  printf("\n");
}
int main(int argc,char**argv){
  char*m=argv[1]; long long steps=atoll(argv[2]); long long t0=atoll(argv[3]);
  for(int i=0;i<6;i++) for(int r=0;r<2;r++){ char*g=m+7*i+3*r; if(g[2]<'A'||g[2]>'F'){S[i][r]=-1;continue;} W[i][r]=g[0]-'0'; D[i][r]=g[1]=='R'?1:-1; S[i][r]=g[2]-'A'; }
  tp=calloc(N,1); int p=N/2,lo=p,hi=p,s=0,pd=0; long long last=-100;
  for(long long t=1;t<=steps;t++){
    int r=tp[p]; if(S[s][r]<0){ printf("HALT %lld\n",t); pr(t,lo,hi,p,s); return 0; }
    int d=D[s][r];
    if(t>t0 && d!=pd && t-last>20 && ((tp[p+1]==0&&tp[p+2]==0&&p+2<=hi)||(tp[p-1]==0&&tp[p-2]==0&&p-2>=lo))){ pr(t,lo,hi,p,s); last=t; }
    tp[p]=W[s][r]; pd=d; p+=d; s=S[s][r]; if(p<lo)lo=p; if(p>hi)hi=p;
  }
  printf("RUNNING\n");
}
