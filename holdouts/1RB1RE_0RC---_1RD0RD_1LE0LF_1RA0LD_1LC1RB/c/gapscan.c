/* gapscan G0 G1 C MAXSTEPS: for each gap size G in [G0,G1], run 1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB from the
 * start configuration S = `1 0 C> 0` followed by `0^G (10)^C 1` and blank tape, cell by cell, until it halts ("HALT"),
 * the head passes the block ("merge": the fresh run inside the gap has reached the block and absorbed it) or
 * MAXSTEPS ("run").  One line per G: "G outcome steps". */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int W[6][2],Mv[6][2],N[6][2];
int main(int argc,char**argv){
 const char*M="1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB";
 for(int i=0;i<6;i++)for(int r=0;r<2;r++){const char*t=M+7*i+3*r; if(t[0]=='-'){N[i][r]=-1;continue;} W[i][r]=t[0]-'0';Mv[i][r]=t[1]=='R'?1:-1;N[i][r]=t[2]-'A';}
 int g0=atoi(argv[1]),g1=atoi(argv[2]),c=atoi(argv[3]); long long maxs=atoll(argv[4]);
 int SZ=1<<22; unsigned char*t=malloc(SZ);
 for(int G=g0;G<=g1;G++){
  memset(t,0,SZ); int base=SZ/2; int p=base; t[p++]=1;t[p++]=0; int head=p; p++; /* head cell 0 */
  p+=G; int blk=p; for(int i=0;i<c;i++){t[p++]=1;t[p++]=0;} t[p++]=1; int end=p;
  int st=2; long long k=0; int halted=0; long long mergek=-1;
  while(k<maxs){ int r=t[head]; if(N[st][r]<0){halted=1;break;} t[head]=W[st][r]; head+=Mv[st][r]; st=N[st][r]; k++;
    if(head>=end+2 && mergek<0){mergek=k;break;}
    if(head<10||head>SZ-10){printf("oob\n");break;} }
  printf("%d %s %lld\n",G,halted?"HALT":(mergek>0?"merge":"run"),k);
 }
}
