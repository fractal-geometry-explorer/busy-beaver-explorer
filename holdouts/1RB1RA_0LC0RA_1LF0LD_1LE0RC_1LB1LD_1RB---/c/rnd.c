// rnd.c SEED NTRIALS NBLOCKS MAXSTEPS MODE: random tapes of odd blocks, start A at left end (mode 0) ; count halts
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static const char *M="1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---";
#define N (1<<22)
static unsigned char tape[N];
int w[6][2],mv[6][2],ns[6][2];
int main(int argc,char**argv){
  int seed=atoi(argv[1]),nt=atoi(argv[2]),nb=atoi(argv[3]); double mx=atof(argv[4]); int mode=atoi(argv[5]);
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*t=M+7*s+3*b; if(t[2]=='-'){ns[s][b]=-1;continue;} w[s][b]=t[0]-'0';mv[s][b]=t[1]=='R'?1:-1;ns[s][b]=t[2]-'A';}
  srand(seed); int halts=0;
  for(int t=0;t<nt;t++){
    memset(tape,0,N); long p0=N/2,q=p0; char desc[4000]; int dl=0;
    for(int i=0;i<nb;i++){ int r=rand()%100; int len;
      if(mode==0) len=1+2*(rand()%3);            // 1,3,5
      else if(mode==1) len=(r<70)?3:(r<85?1:5);   // mostly 3
      else if(mode==2) len=1+2*(rand()%4);       // 1,3,5,7
      else len=1+rand()%5;                       // any 1..5 (even too)
      for(int j=0;j<len;j++)tape[q++]=1; q++; if(dl<3900)dl+=sprintf(desc+dl,"%d ",len);}
    long p=p0; int st=0; unsigned long long k=0; int h=0;
    while(k<mx){ int b=tape[p]; if(ns[st][b]<0){h=1;break;} tape[p]=w[st][b]; p+=mv[st][b]; st=ns[st][b]; k++; if(p<8||p>N-8)break; }
    if(h){halts++; if(halts<=5)printf("HALT trial %d step %llu: %s\n",t,k,nb<=40?desc:"");}
  }
  printf("mode %d blocks %d trials %d halts %d\n",mode,nb,nt,halts);
}
