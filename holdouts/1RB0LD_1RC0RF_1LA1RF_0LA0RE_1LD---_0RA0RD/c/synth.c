// reads lines: left-cells string (0/1); runs mirrored-c2 or c1 from sample state on blank right; prints halts
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<22)
static unsigned char tape[N];
int main(int argc,char**argv){
  const char*tm=argv[1]; int Q=argv[2][0]-'A'; long maxs=atol(argv[3]);
  int w[6][2],mv[6][2],nx[6][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*p=tm+s*7+b*3; if(p[0]=='-'){nx[s][b]=-1;continue;} w[s][b]=p[0]-'0'; mv[s][b]=p[1]=='R'?1:-1; nx[s][b]=p[2]-'A';}
  static char line[1<<16]; int lo=1,hi=0; long nh=0,nl=0,nesc=0;
  while(fgets(line,sizeof line,stdin)){
    int n=strlen(line); while(n&&(line[n-1]=='\n'))n--;
    int base=N/2; if(lo<hi)memset(tape+lo,0,hi-lo+1); lo=hi=base; for(int i=0;i<n;i++)tape[base+i]=line[i]-'0';
    int pos=base+n,st=Q; hi=pos; long t=0; int halted=0;
    for(;t<maxs;t++){int b=tape[pos]; if(nx[st][b]<0){halted=1;break;} tape[pos]=w[st][b]; pos+=mv[st][b]; if(pos<lo)lo=pos; if(pos>hi)hi=pos; st=nx[st][b]; if(pos<8||pos>N-8){nesc++;break;}}
    nl++; if(halted){nh++; line[n]=0; printf("HALT %ld %s\n",t,line);}
  }
  fprintf(stderr,"lines %ld halts %ld esc %ld\n",nl,nh,nesc); return 0;}
