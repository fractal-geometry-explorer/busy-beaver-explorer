// dump tape at each event: state E arrives left of the visited tape. usage: dump MAXSTEPS [FROMSTEP]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static const char *M="1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---";
#define N (1<<26)
static unsigned char tape[N];
int main(int argc,char**argv){
  double mx=atof(argv[1]); double from=argc>2?atof(argv[2]):0;
  int w[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*t=M+7*s+3*b; if(t[2]=='-'){ns[s][b]=-1;continue;} w[s][b]=t[0]-'0';mv[s][b]=t[1]=='R'?1:-1;ns[s][b]=t[2]-'A';}
  long p=N/2,lo=p,hi=p; int st=0; unsigned long long k=0; unsigned long long ev=0;
  while(k<mx){
    int b=tape[p]; if(ns[st][b]<0){printf("HALT %llu\n",k);return 0;}
    tape[p]=w[st][b]; p+=mv[st][b]; st=ns[st][b]; k++;
    if(p>hi)hi=p;
    if(p<lo){ if(st==4){ ev++; if(k>=from){ printf("%llu %llu %ld %ld ",ev,k,lo-N/2,hi-N/2); for(long i=lo;i<=hi;i++)putchar('0'+tape[i]); putchar('\n');} } lo=p; }
  }
  fprintf(stderr,"END %llu events %llu lo %ld hi %ld\n",k,ev,lo-N/2,hi-N/2);
}
