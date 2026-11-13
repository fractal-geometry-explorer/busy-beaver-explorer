// hsearch MACHINE MAXSTEPS < lines of 0/1 strings: for each start tape (head in D on its first cell), print the line if the machine halts within MAXSTEPS
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<20)
unsigned char tape[N]; char line[100000];
int main(int argc,char**argv){
  char*m=argv[1]; long long maxs=atoll(argv[2]); int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*t=m+s*7+r*3; if(t[0]=='-'){ns[s][r]=-1;continue;} nw[s][r]=t[0]-'0'; mv[s][r]=t[1]=='R'?1:-1; ns[s][r]=t[2]-'A';}
  while(fgets(line,sizeof line,stdin)){
    int L=strlen(line); while(L&&(line[L-1]=='\n'))line[--L]=0; char*sp=strchr(line,' '); char*bits=sp?sp+1:line;
    memset(tape,0,N); long pos=N/2; for(int i=0;bits[i];i++)tape[pos+i]=bits[i]-'0';
    int st=3; long long i; int halted=0;
    for(i=0;i<maxs;i++){int r=tape[pos]; int n=ns[st][r]; if(n<0){halted=1;break;} tape[pos]=nw[st][r]; pos+=mv[st][r]; st=n; if(pos<2||pos>N-2)break;}
    if(halted) printf("HALT %lld %s\n",i,line);
  }
  return 0;}
