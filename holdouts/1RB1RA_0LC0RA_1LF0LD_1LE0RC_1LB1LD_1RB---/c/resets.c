// resets.c MAXSTEPS: events (E steps off the left end); prints reset events (tape starts 100) and every event longer than 1/8 of the run so far
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static const char *M="1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---";
#define N (1<<26)
static unsigned char tape[N];
int main(int argc,char**argv){
  double mx=atof(argv[1]);
  int w[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*t=M+7*s+3*b; if(t[2]=='-'){ns[s][b]=-1;continue;} w[s][b]=t[0]-'0';mv[s][b]=t[1]=='R'?1:-1;ns[s][b]=t[2]-'A';}
  long p=N/2,lo=p,hi=p; int st=0; unsigned long long k=0,ev=0,last=0,e0=0,b0=0,c0=0;
  while(k<mx){
    int b=tape[p]; if(ns[st][b]<0){printf("HALT %llu\n",k);return 0;}
    if(b==0){ if(st==4){e0++; if(tape[p-1]==0&&p-1>lo+2&&p<hi-2){b0++; printf("E00 step %llu pos %ld of %ld ctx %d%d%d%d%d%d[0]%d%d\n",k,p-lo,hi-lo,tape[p-6],tape[p-5],tape[p-4],tape[p-3],tape[p-2],tape[p-1],tape[p+1],tape[p+2]);} } }
    tape[p]=w[st][b]; p+=mv[st][b]; st=ns[st][b]; k++;
    if(p>hi)hi=p;
    if(p<lo){ if(st==4){ ev++; int reset=(tape[lo]==1&&tape[lo+1]==0&&tape[lo+2]==0);
        if(reset|| (k-last)*8>k){ printf("%s ev %llu step %llu dur %llu lo %ld hi %ld E0 %llu E00inner %llu | ",reset?"RESET":"LONG",ev,k,k-last,lo-N/2,hi-N/2,e0,b0); for(long i=lo;i<=hi&&i<lo+3000;i++)putchar('0'+tape[i]); putchar('\n'); fflush(stdout);} 
        last=k; } lo=p; }
  }
  printf("END %llu events %llu lo %ld hi %ld E0 %llu E00inner %llu\n",k,ev,lo-N/2,hi-N/2,e0,b0);
}
