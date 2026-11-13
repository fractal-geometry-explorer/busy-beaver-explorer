// edges MACHINE STEPS [MAXLINES] [T]: print "step side state tape" each time the head arrives at an edge of the
// visited region after being at the opposite edge (a full sweep); with T>0, at every turn of the head after a run of
// at least T cells instead. The tape is printed as a raw 0/1 string from lo to hi, with ">" before the head cell.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<24)
unsigned char tape[N]; 
int main(int argc,char**argv){
  char*m=argv[1]; long long steps=atoll(argv[2]); long maxl=argc>3?atol(argv[3]):1000000; long T=argc>4?atol(argv[4]):0; long lastturn=N/2; int dir=1;
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*t=m+s*7+r*3; if(t[0]=='-'){ns[s][r]=-1;continue;} nw[s][r]=t[0]-'0'; mv[s][r]=t[1]=='R'?1:-1; ns[s][r]=t[2]-'A';}
  long pos=N/2,lo=pos,hi=pos; int st=0; int last=0; long lines=0; long prevpos=pos;
  for(long long i=0;i<steps;i++){
    int r=tape[pos]; int n=ns[st][r]; if(n<0){printf("HALT %lld\n",i);return 0;}
    tape[pos]=nw[st][r]; pos+=mv[st][r]; st=n;
    if(pos<lo)lo=pos; if(pos>hi)hi=pos;
    if(pos<=2||pos>=N-2){printf("OUT\n");return 0;}
    int side=0; int print=0;
    if(T==0){ if(pos==lo)side=-1; else if(pos==hi)side=1; if(side&&side!=last){last=side;print=1;} }
    else { int nd=pos>prevpos?1:-1; if(nd!=dir){ long len=labs(prevpos-lastturn); if(len>=T){print=1; side=dir;} lastturn=prevpos; dir=nd; } }
    prevpos=pos;
    if(print){
      printf("%lld %c %c ",i+1,side<0?'L':'R','A'+st);
      for(long p=lo;p<=hi;p++){ if(p==pos)putchar('>'); putchar('0'+tape[p]);} putchar('\n');
      if(++lines>=maxl)return 0;}
  }
  return 0;}
