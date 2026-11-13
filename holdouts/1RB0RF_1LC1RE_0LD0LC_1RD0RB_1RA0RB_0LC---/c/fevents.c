// Direct run from blank tape: print the step of every event "state A reads a 1" (the only way into F, and so the
// only way to halt), and HALT if it halts.  usage: fevents MACHINE STEPS   (used by py/validate.py)
#include <stdio.h>
#include <stdlib.h>
int W[6][2],M[6][2],S[6][2];
void parse(const char*s){for(int i=0;i<6;i++)for(int b=0;b<2;b++){const char*x=s+7*i+3*b; if(x[2]=='-'){S[i][b]=-1;continue;} W[i][b]=x[0]-'0';M[i][b]=x[1]=='R'?1:-1;S[i][b]=x[2]-'A';}}
#define N (1<<22)
unsigned char tape[N];
int main(int argc,char**argv){
  parse(argv[1]); long long maxs=atoll(argv[2]);
  int pos=N/2,st=0;
  for(long long n=0;n<maxs;n++){
    int sym=tape[pos];
    if(st==0&&sym==1){printf("%lld\n",n);fflush(stdout);}
    if(S[st][sym]<0){printf("HALT %lld\n",n+1);return 0;}
    int s2=S[st][sym]; tape[pos]=W[st][sym]; pos+=M[st][sym]; st=s2;
    if(pos<16||pos>N-16){printf("OUT %lld\n",n);return 0;}
  }
  printf("END %lld\n",maxs); return 0;
}
