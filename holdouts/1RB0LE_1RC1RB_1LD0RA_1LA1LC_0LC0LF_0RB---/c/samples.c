// samples MACHINE STEPS STATE L|R MINSTEP MAXLINES: each time the head is in STATE (or * any) at that end of the
// visited tape, print the step and the tape as alternating runs ("1k" k ones, "0j" j zeros). Plain simulator.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<24)
unsigned char tape[N];
int nx[6][2],wr[6][2],mv[6][2];
int main(int argc,char**argv){
  char*m=argv[1]; long long S=atoll(argv[2]); char st=argv[3][0]; char side=argv[4][0]; long long mins=atoll(argv[5]); long maxl=atol(argv[6]);
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*p=m+s*7+b*3; if(p[2]=='-'){nx[s][b]=-1;continue;} wr[s][b]=p[0]-'0'; mv[s][b]=p[1]=='R'?1:-1; nx[s][b]=p[2]-'A';}
  long pos=N/2,lo=pos,hi=pos; int s=0; long lines=0;
  for(long long t=0;t<S;t++){
    int b=tape[pos];
    if(t>=mins && (st=='*'||s==st-'A') && ((side=='L'&&pos==lo)||(side=='R'&&pos==hi))){
      printf("%lld %c%d |",t,'A'+s,b);
      // runs
      long i=lo; 
      while(i<=hi){ int v=tape[i]; long j=i; while(j<=hi&&tape[j]==v)j++; 
        // compress repeated pairs
        printf(" %c%ld",v?'1':'0',j-i); i=j;}
      printf("\n"); if(++lines>=maxl)return 0;
    }
    if(nx[s][b]<0){printf("HALT %lld\n",t);return 0;}
    tape[pos]=wr[s][b]; pos+=mv[s][b]; s=nx[s][b]; if(pos<lo)lo=pos; if(pos>hi)hi=pos;
  }
}
