/* Independent direct simulator (written for the cross-check, shares no code with tools/).
   usage: sim TNF MAXSTEPS   -> prints "halt <steps> <state><symbol> <ones>" or "nohalt <steps> <left> <right>"
   Halting convention (bbchallenge): the halting transition counts as a step. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define TAPE (1<<26)
int main(int argc,char**argv){
  if(argc<3){fprintf(stderr,"usage\n");return 2;}
  const char*s=argv[1]; unsigned long long maxs=strtoull(argv[2],0,10);
  int wr[6][2],mv[6][2],nx[6][2];
  int n=strlen(s); if(n!=6*7-1){fprintf(stderr,"bad tnf\n");return 2;}
  for(int q=0;q<6;q++)for(int b=0;b<2;b++){const char*t=s+q*7+b*3;
    if(t[0]=='-'){nx[q][b]=-1;wr[q][b]=1;mv[q][b]=1;continue;}
    wr[q][b]=t[0]-'0'; mv[q][b]=(t[1]=='R')?1:-1; nx[q][b]=t[2]-'A';
    if(t[1]!='R'&&t[1]!='L'){fprintf(stderr,"bad move\n");return 2;}}
  unsigned char*tape=calloc(TAPE,1); long p=TAPE/2,lo=p,hi=p; int q=0;
  for(unsigned long long i=0;i<maxs;i++){
    int b=tape[p];
    if(nx[q][b]<0){ long ones=0; for(long j=lo;j<=hi;j++)ones+=tape[j];
      printf("halt %llu %c%d %ld\n",i+1,'A'+q,b,ones+1); return 0;}
    tape[p]=wr[q][b]; p+=mv[q][b]; q=nx[q][b];
    if(p<lo)lo=p; if(p>hi)hi=p;
    if(p<=0||p>=TAPE-1){printf("tape_overflow %llu\n",i+1);return 1;}
  }
  printf("nohalt %llu %ld %ld\n",maxs,TAPE/2-lo,hi-TAPE/2); return 0;
}
