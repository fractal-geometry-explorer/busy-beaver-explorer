// phasemap NMAX LIMIT [NMIN]: the phase map of 1RB0LE_1RC1RE_0RD1RC_1LA0LB_1LF0RB_---1LD. For each N, start from F at the
// left end on a tape that is a single run of ones (print N -> N' and steps), or a halt, or LIMIT steps.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define W (1<<20)
unsigned char tape[W]; int nx[6][2],wr[6][2],mv[6][2];
const char*M="1RB0LE_1RC1RE_0RD1RC_1LA0LB_1LF0RB_---1LD";
int main(int argc,char**argv){int NM=atoi(argv[1]); long long LIM=atoll(argv[2]); int N0=argc>3?atoi(argv[3]):1;
 for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*p=M+s*7+b*3; if(p[2]=='-'){nx[s][b]=-1;continue;} wr[s][b]=p[0]-'0'; mv[s][b]=p[1]=='R'?1:-1; nx[s][b]=p[2]-'A';}
 for(int N=N0;N<=NM;N++){ memset(tape,0,sizeof tape); long lo=W/2,hi=lo+N-1; for(long i=lo;i<=hi;i++)tape[i]=1; long pos=lo; int s=5; long long t;
  int done=0;
  for(t=0;t<LIM;t++){ int b=tape[pos];
    if(t>0 && s==5 && pos==lo && b==1){ long i=lo; while(i<=hi&&tape[i])i++; if(i>hi){printf("%d -> %ld  steps %lld\n",N,hi-lo+1,t);done=1;break;} }
    if(nx[s][b]<0){printf("%d -> HALT at step %lld\n",N,t+1);done=1;break;}
    tape[pos]=wr[s][b]; pos+=mv[s][b]; s=nx[s][b]; if(pos<lo)lo=pos; if(pos>hi)hi=pos; }
  if(!done)printf("%d -> ? (limit)\n",N);}
}
