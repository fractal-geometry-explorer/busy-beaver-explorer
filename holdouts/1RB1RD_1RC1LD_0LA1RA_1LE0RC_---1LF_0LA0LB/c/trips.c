// trips MACHINE TAPE MAXSTEPS STATE: start 0^inf STATE> 0 TAPE; at each new left end print step, state, left end, rightmost cell reached since the last STATE line, tape
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<25)
static unsigned char tape[N];
int main(int c,char**v){
  char*m=v[1]; char*T=v[2]; long long S=atoll(v[3]); int ST=v[4][0]-'A';
  int w[6][2],d[6][2],ns[6][2];
  for(int i=0;i<6;i++)for(int b=0;b<2;b++){char*s=m+7*i+3*b; if(s[2]=='-'){ns[i][b]=-1;continue;} w[i][b]=s[0]-'0'; d[i][b]=s[1]=='R'?1:-1; ns[i][b]=s[2]-'A';}
  long long lo=N-4000000, p=lo+1; for(char*q=T;*q;q++) tape[p++]=*q-'0';
  long long pos=lo, hi=p, mx=lo; int st=ST;
  for(long long n=1;n<=S;n++){
    int b=tape[pos]; int t=ns[st][b]; if(t<0){printf("HALT %lld\n",n);return 0;}
    tape[pos]=w[st][b]; pos+=d[st][b]; st=t;
    if(pos>hi)hi=pos; if(pos>mx)mx=pos;
    if(pos<lo){lo=pos; printf("%lld %c %lld %lld ",n,(char)(65+st),lo,mx); for(long long i=lo+1;i<=hi;i++)putchar(48+tape[i]); putchar(10); if(st==ST) mx=lo;}
  }
  return 0;
}
