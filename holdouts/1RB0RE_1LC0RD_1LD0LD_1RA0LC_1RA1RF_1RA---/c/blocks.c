// The block list of 1RB0RE_1LC0RD_1LD0LD_1RA0LC_1RA1RF_1RA--- at every left turn of the head (one line per sweep):
// step, offset, state, then the tape from its left end as tokens: Tk = (10)^k, and single cells 0 / 1.
// usage: gcc -O2 -o blocks blocks.c && ./blocks 300000000 0 > blocks.txt     (a few seconds)
//        python3 ../py/ticks.py blocks.txt
#include <stdio.h>
#include <stdlib.h>
#define N (1<<24)
static unsigned char t[N];
int main(int argc,char**argv){
  const char*m="1RB0RE_1LC0RD_1LD0LD_1RA0LC_1RA1RF_1RA---"; long long S=atoll(argv[1]); long long from=atoll(argv[2]);
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){const char*p=m+s*7+r*3; if(p[0]=='-'){ns[s][r]=-1;continue;} nw[s][r]=p[0]-'0';mv[s][r]=p[1]=='R'?1:-1;ns[s][r]=p[2]-'A';}
  long pos=N/2,lo=pos,hi=pos;int st=0,pd=0;
  for(long long i=0;i<S;i++){int r=t[pos];int q=ns[st][r]; if(q<0){printf("halt %lld\n",i);return 0;}
    t[pos]=nw[st][r]; int d=mv[st][r];
    if(pd==-1&&d==1&&pos<=lo+2&&i>=from){ printf("%lld %ld %c ",i,pos-lo,'A'+st);
      long j=lo; while(j<=hi){ if(t[j]==1&&j+1<=hi&&t[j+1]==0){long k=0; while(j+1<=hi&&t[j]==1&&t[j+1]==0){k++;j+=2;} printf("T%ld ",k);} else {putchar('0'+t[j]); putchar(' '); j++;} }
      putchar('\n');}
    pd=d; pos+=d; st=q; if(pos<lo)lo=pos; if(pos>hi)hi=pos;}
  return 0;}
