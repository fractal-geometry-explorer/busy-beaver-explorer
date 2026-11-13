// m6phase N TAIL [K]: start from 0^inf E> 0 0 1^N TAIL 0^inf (TAIL a 0/1 string) and print the next K phase
// starts: the head in C on a new left cell, followed by 1^l or 10 1^(l-2) with l >= 7.  Each line: steps, l, "a" if the
// second form, and the rest of the tape after the ones (the tail).  From blank tape the first phase start, at step 3920,
// is 0^inf E> 0 0 1^86, so "m6phase 86 \"\" 16" follows the run of the machine (steps counted from step 3920).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define SZ (1<<26)
static unsigned char t[SZ];
int main(int argc,char**argv){
  const char*m="1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA";
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){const char*x=m+s*7+r*3; if(x[0]=='-'){ns[s][r]=-1;continue;} nw[s][r]=x[0]-'0'; mv[s][r]=x[1]=='R'?1:-1; ns[s][r]=x[2]-'A';}
  long N=atol(argv[1]); const char*T=argc>2?argv[2]:""; int K=argc>3?atoi(argv[3]):1;
  long p=SZ/2, lo=p, hi; long q=p+2; for(long i=0;i<N;i++) t[q++]=1; for(const char*c=T;*c;c++) t[q++]=*c-'0'; hi=q-1;
  setvbuf(stdout,NULL,_IONBF,0); int st=4; long long steps=0; int got=0;
  while(got<K){
    int r=t[p]; int n=ns[st][r]; if(n<0){printf("HALT steps %lld\n",steps); return 0;}
    t[p]=nw[st][r]; p+=mv[st][r]; st=n; steps++;
    if(p>hi) hi=p;
    if(p<lo){ lo=p; if(st==2 && t[p+1]==1){ long i=p+1,n1=0,form=0; if(t[p+2]==0){form=1;i=p+3;} while(t[i]==1){n1++;i++;}
        if(n1>=5){ printf("%lld %ld %s ",steps,n1+(form?2:0),form?"a":"-"); for(;i<=hi;i++) putchar('0'+t[i]); putchar('\n'); got++; }}}
    if(p<100||p>SZ-100){printf("OUT\n");return 0;}
  }
  return 0;}
