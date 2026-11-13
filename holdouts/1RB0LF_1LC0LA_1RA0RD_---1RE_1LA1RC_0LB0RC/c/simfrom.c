// simfrom MACHINE TAPE HEAD STATE MAXSTEPS ST SIDE : run from given tape; print tape when head in ST at L/R end
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<26)
unsigned char tape[N];
int W[6][2],Mv[6][2],Nx[6][2];
int main(int argc,char**argv){
  char*m=argv[1]; char*tp=argv[2]; long long h=atoll(argv[3]); int st=argv[4][0]-'A'; long long max=atoll(argv[5]);
  int AS=argv[6][0]-'A', ASIDE=argv[7][0]=='R';
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*p=m+s*7+b*3; if(p[0]=='-'){Nx[s][b]=-1;continue;} W[s][b]=p[0]-'0';Mv[s][b]=p[1]=='R'?1:-1;Nx[s][b]=p[2]-'A';}
  long long L=strlen(tp); long long base=N/2; for(long long i=0;i<L;i++) tape[base+i]=tp[i]-'0';
  long long lo=base,hi=base+L-1,pos=base+h;
  for(long long t=1;t<=max;t++){
    int b=tape[pos]; if(Nx[st][b]<0){printf("HALT %lld %c %lld\n",t,'A'+st,pos-lo);return 0;}
    tape[pos]=W[st][b]; pos+=Mv[st][b]; st=Nx[st][b];
    if(pos<lo)lo=pos; if(pos>hi)hi=pos;
    if(pos<=0||pos>=N-1){printf("OOB\n");return 1;}
    if(st==AS&&pos==(ASIDE?hi:lo)){printf("%lld %c %lld ",t,'A'+st,pos-lo); for(long long i=lo;i<=hi;i++)putchar('0'+tape[i]); putchar('\n');}
  }
  printf("END\n");
}
