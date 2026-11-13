// rounds MACHINE STEPS: plain simulator; prints the step and the run-length tape at every round start (state A on the left end of the tape, reading 0 0 0), to compare with py/accel.py --rounds.
#include <stdio.h>
#include <stdlib.h>
#define N (1<<28)
int W[6][2],D[6][2],S[6][2];
unsigned char *tp;
void pr(long long t,int lo,int hi,int p,int s){
  printf("%lld ",t);
  int i=lo;
  while(i<=hi){ if(i==p) printf("%c> ","ABCDEF"[s]); int j=i; while(j<=hi && tp[j]==tp[i] && !(j>i && j==p)) j++; if(j-i==1) printf("%d ",tp[i]); else printf("%d^%d ",tp[i],j-i); i=j; }
  printf("\n");
}
int main(int argc,char**argv){
  char*m=argv[1]; long long steps=atoll(argv[2]); 
  for(int i=0;i<6;i++) for(int r=0;r<2;r++){ char*g=m+7*i+3*r; if(g[2]<'A'||g[2]>'F'){S[i][r]=-1;continue;} W[i][r]=g[0]-'0'; D[i][r]=g[1]=='R'?1:-1; S[i][r]=g[2]-'A'; }
  tp=calloc(N,1); int p=N/2,lo=p,hi=p,s=0;
  for(long long t=0;t<steps;t++){
    int r=tp[p]; if(S[s][r]<0){ printf("HALT %lld\n",t); pr(t,lo,hi,p,s); return 0; }
    if(r==0 && s==0 && p<=lo && tp[p+1]==0 && tp[p+2]==0) pr(t,lo<p?lo:p,hi,p,s);
    tp[p]=W[s][r]; p+=D[s][r]; s=S[s][r];
    if(p<lo)lo=p; if(p>hi)hi=p;
  }
}
