// hturn MACHINE STEPS H [MAXLINES] [FROM]: print "step side state extent distance tape" each time the head turns back by H cells from its furthest point (a turn with hysteresis H); the tape is printed from the leftmost to the rightmost visited cell with > before the head cell.
#include <stdio.h>
#include <stdlib.h>
#define N (1<<26)
unsigned char tape[N];
int main(int argc,char**argv){char*m=argv[1]; long long steps=atoll(argv[2]); long H=atol(argv[3]); long maxl=argc>4?atol(argv[4]):1000000; long long from=argc>5?atoll(argv[5]):0;
 int nw[6][2],mv[6][2],ns[6][2];
 for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*t=m+s*7+r*3; if(t[0]=='-'){ns[s][r]=-1;continue;} nw[s][r]=t[0]-'0'; mv[s][r]=t[1]=='R'?1:-1; ns[s][r]=t[2]-'A';}
 long pos=N/2,lo=pos,hi=pos; int st=0; int dir=1; long ext=pos; long lines=0; long lastturn=pos;
 for(long long i=0;i<steps;i++){int r=tape[pos]; int n=ns[st][r]; if(n<0){printf("HALT %lld\n",i+1);return 0;}
  tape[pos]=nw[st][r]; pos+=mv[st][r]; st=n; if(pos<lo)lo=pos; if(pos>hi)hi=pos;
  if(dir==1){ if(pos>ext)ext=pos; else if(pos<=ext-H){ if(i+1>=from){printf("%lld R %c %ld %ld ",i+1,'A'+st,ext-lo,labs(ext-lastturn)); for(long p=lo;p<=hi;p++){if(p==pos)putchar('>');putchar('0'+tape[p]);} putchar('\n'); if(++lines>=maxl)return 0;} lastturn=ext; dir=-1; ext=pos;} }
  else { if(pos<ext)ext=pos; else if(pos>=ext+H){ if(i+1>=from){printf("%lld L %c %ld %ld ",i+1,'A'+st,ext-lo,labs(ext-lastturn)); for(long p=lo;p<=hi;p++){if(p==pos)putchar('>');putchar('0'+tape[p]);} putchar('\n'); if(++lines>=maxl)return 0;} lastturn=ext; dir=1; ext=pos;} }
 }}
