// Print the configuration (run-length coded, head as [S b]) at each of the given steps from blank tape.
// usage: dump MACHINE STEP1 STEP2 ...   (used to compare the epoch starts with 1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF)
#include <stdio.h>
#include <stdlib.h>
int main(int argc,char**argv){
  char*M=argv[1]; int wr[8][2],mv[8][2],nx[8][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*t=M+s*7+b*3; if(t[2]=='-'){nx[s][b]=-1;continue;} wr[s][b]=t[0]-'0'; mv[s][b]=t[1]=='R'?1:-1; nx[s][b]=t[2]-'A';}
  long SZ=1<<26; unsigned char*tape=calloc(SZ,1); long p=SZ/2,lo=p,hi=p; int s=0; long long i=0;
  for(int a=2;a<argc;a++){ long long N=atoll(argv[a]);
    for(;i<N;i++){int b=tape[p]; if(nx[s][b]<0){printf("HALT %lld\n",i+1);return 0;} tape[p]=wr[s][b]; p+=mv[s][b]; s=nx[s][b]; if(p<lo)lo=p; if(p>hi)hi=p;}
    printf("%lld %c%d w=%ld pos=%ld :",i,'A'+s,tape[p],hi-lo+1,p-SZ/2);
    long x=lo; while(x<=hi){ if(x==p){printf(" [%c%d]",'A'+s,tape[x]);x++;continue;} long y=x; while(y<=hi&&y!=p&&tape[y]==tape[x])y++; if(y-x==1)printf(" %d",tape[x]); else printf(" %d^%ld",tape[x],y-x); x=y;}
    printf("\n");}
}
