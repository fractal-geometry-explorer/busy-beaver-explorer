// phases MACHINE FROM TO: at each time the head is at an end of the visited tape (more than 20 steps after the last), print
// step, side, state, length, the defect positions (cells i with t[i] != t[i-3], from the left end) and the first 50 cells.
// Build: gcc -O2 -o phases phases.c ; ./phases 1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA 0 15000000000 > rd.txt ; python3 ../py/phases.py rd.txt
#include <stdio.h>
#include <stdlib.h>
#define N (1<<27)
static unsigned char tape[N];
int main(int c,char**v){
  char*m=v[1]; long long S0=atoll(v[2]), S=atoll(v[3]);
  int w[6][2],d[6][2],ns[6][2];
  for(int i=0;i<6;i++)for(int b=0;b<2;b++){char*s=m+7*i+3*b; if(s[2]=='-'){ns[i][b]=-1;continue;} w[i][b]=s[0]-'0'; d[i][b]=s[1]=='R'?1:-1; ns[i][b]=s[2]-'A';}
  long long pos=N/2,lo=pos,hi=pos,last=0; int st=0;
  for(long long n=1;n<=S;n++){
    int b=tape[pos]; int t=ns[st][b]; if(t<0){printf("HALT %lld\n",n);return 0;}
    tape[pos]=w[st][b]; pos+=d[st][b]; st=t;
    if(pos<lo)lo=pos; if(pos>hi)hi=pos;
    if(n>=S0 && (pos==hi||pos==lo)){ if(n-last>20){
      printf("%lld %c %c %lld:", n, pos==hi?'R':'L','A'+st, hi-lo+1);
      int cnt=0;
      for(long long i=lo+3;i<=hi-6;i++) if(tape[i]!=tape[i-3]) { if(cnt++<30) printf(" %lld", i-lo); }
      printf(" |"); for(long long i=lo;i<lo+50&&i<=hi;i++) putchar(48+tape[i]); printf("\n");}
      last=n;}
  }
  return 0;
}
