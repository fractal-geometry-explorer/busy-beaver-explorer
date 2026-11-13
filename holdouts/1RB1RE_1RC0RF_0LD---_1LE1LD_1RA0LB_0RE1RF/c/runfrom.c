// runfrom: plain simulator started from a given tape.  runfrom MACHINE STATE MAXSTEPS < TAPE
// TAPE is one line of 0s and 1s, the head starts on its first cell in STATE.  Prints "HALT at step ..." or
// "END steps state head" and the first 200 visited cells.  Used by py/closure/screen.py zone.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define N (1<<26)
static uint8_t *tape; static char buf[1<<25];
int main(int argc,char**argv){
  const char*m=argv[1]; int st=argv[2][0]-'A'; uint64_t maxs=strtoull(argv[3],0,10);
  int W[6][2],D[6][2],S[6][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*p=m+s*7+b*3; if(p[0]=='-'){W[s][b]=1;D[s][b]=1;S[s][b]=6;}else{W[s][b]=p[0]-'0';D[s][b]=p[1]=='R'?1:-1;S[s][b]=p[2]-'A';}}
  tape=calloc(N,1); if(!fgets(buf,sizeof buf,stdin))return 1; long n=strlen(buf); while(n&&(buf[n-1]<'0'||buf[n-1]>'1'))n--;
  long pos=N/2,lo=pos,hi=pos+n-1; for(long i=0;i<n;i++)tape[pos+i]=buf[i]-'0'; uint64_t t=0;
  while(t<maxs){ int b=tape[pos]; int ns=S[st][b]; if(ns==6){printf("HALT at step %llu state %c head offset %ld (tape %ld..%ld)\n",(unsigned long long)t,'A'+st,pos-lo,lo-N/2,hi-N/2);return 0;}
    tape[pos]=W[st][b]; pos+=D[st][b]; st=ns; t++; if(pos<lo)lo=pos; if(pos>hi)hi=pos; }
  printf("END %llu %c %ld ",(unsigned long long)t,'A'+st,pos-lo); for(long i=lo;i<=hi && i<lo+200;i++)putchar('0'+tape[i]); putchar('\n');
}
