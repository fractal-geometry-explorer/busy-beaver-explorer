// pert.c TAPEFILE NTRIALS MAXSTEPS SEED MODE: line "ev step lo hi tape" (state E on the first cell... head one cell left of the tape, state E).
// MODE 0: flip one random cell; 1: delete one cell; 2: insert a 0; 3: insert a 1; 4: flip two cells; 5: replace a random 1 by 0 next to a 0 (make 00)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static const char *M="1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---";
#define N (1<<22)
static unsigned char tape[N]; static char buf[1<<21]; static char cur[1<<21];
int w[6][2],mv[6][2],ns[6][2];
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); int nt=atoi(argv[2]); double mx=atof(argv[3]); srand(atoi(argv[4])); int mode=atoi(argv[5]);
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*t=M+7*s+3*b; if(t[2]=='-'){ns[s][b]=-1;continue;} w[s][b]=t[0]-'0';mv[s][b]=t[1]=='R'?1:-1;ns[s][b]=t[2]-'A';}
  unsigned long long ev,st0; long lo,hi; 
  while(fscanf(f,"%llu %llu %ld %ld %s",&ev,&st0,&lo,&hi,buf)==5){
    int L=strlen(buf); int halts=0; unsigned long long hmin=~0ULL,hmax=0;
    for(int t=0;t<nt;t++){
      strcpy(cur,buf); int L2=L; int i=1+rand()%(L-3);
      if(mode==0) cur[i]^=1;
      else if(mode==1){ memmove(cur+i,cur+i+1,L-i); L2--; }
      else if(mode==2||mode==3){ memmove(cur+i+1,cur+i,L-i+1); cur[i]=mode==2?'0':'1'; L2++; }
      else if(mode==4){ cur[i]^=1; cur[1+rand()%(L-3)]^=1; }
      else if(mode==5){ while(!(cur[i]=='1'&&cur[i+1]=='0')) i=1+rand()%(L-3); cur[i]='0'; }
      memset(tape,0,N); long p0=N/2; for(int j=0;j<L2;j++)tape[p0+j]=cur[j]-'0';
      long p=p0-1; int st=4; unsigned long long k=0; int h=0;   // E one cell left of the tape, as at the event
      if(nt==1&&mode==-1){} 
      while(k<mx){ int b=tape[p]; if(ns[st][b]<0){h=1;break;} tape[p]=w[st][b]; p+=mv[st][b]; st=ns[st][b]; k++; if(p<8||p>N-8)break; }
      if(h){halts++; if(k<hmin)hmin=k; if(k>hmax)hmax=k;}
    }
    printf("event %llu step %llu len %d mode %d trials %d halts %d",ev,st0,L,mode,nt,halts); if(halts)printf(" (halting step %llu..%llu)",hmin,hmax); printf("\n");
  }
}
