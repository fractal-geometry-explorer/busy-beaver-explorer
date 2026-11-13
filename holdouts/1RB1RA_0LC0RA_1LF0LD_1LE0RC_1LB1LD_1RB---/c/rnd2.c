// rnd2.c SEED NTRIALS LEN MAXSTEPS P1: random bit tapes (prob of 1 = P1 percent), random head position and state
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static const char *M="1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---";
#define N (1<<22)
static unsigned char tape[N];
int w[6][2],mv[6][2],ns[6][2];
int main(int argc,char**argv){
  int seed=atoi(argv[1]),nt=atoi(argv[2]),len=atoi(argv[3]); double mx=atof(argv[4]); int p1=atoi(argv[5]);
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*t=M+7*s+3*b; if(t[2]=='-'){ns[s][b]=-1;continue;} w[s][b]=t[0]-'0';mv[s][b]=t[1]=='R'?1:-1;ns[s][b]=t[2]-'A';}
  srand(seed); int halts=0; unsigned long long hist[8]={0};
  for(int t=0;t<nt;t++){
    memset(tape,0,N); long p0=N/2;
    for(int i=0;i<len;i++) tape[p0+i]=(rand()%100)<p1;
    long p=p0+rand()%(len+1); int st=rand()%6; int st0=st; long pp=p-p0; unsigned long long k=0; int h=0;
    while(k<mx){ int b=tape[p]; if(ns[st][b]<0){h=1;break;} tape[p]=w[st][b]; p+=mv[st][b]; st=ns[st][b]; k++; if(p<8||p>N-8)break; }
    if(h){halts++; int b=0; unsigned long long kk=k; while(kk>=10){kk/=10;b++;} if(b>7)b=7; hist[b]++; if(k>100000)printf("late HALT trial %d step %llu start %c pos %ld\n",t,k,'A'+st0,pp);}
  }
  printf("len %d p1 %d trials %d halts %d by decade:",len,p1,nt,halts); for(int i=0;i<8;i++)printf(" %llu",hist[i]); printf("\n");
}
