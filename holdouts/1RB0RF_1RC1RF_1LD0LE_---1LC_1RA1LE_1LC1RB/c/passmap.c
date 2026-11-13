// passmap LO HI: for each n in LO..HI, run 1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB from P(n) = 0^inf 1^n B> 0^inf
// until the tape is again 0^inf 1^m B> 0^inf; prints "n m steps", or "n H steps" if the machine halts.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static const char*M="1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB";
int nw[6][2],mv[6][2],ns[6][2];
int main(int argc,char**argv){
  int lo0=atoi(argv[1]), nmax=atoi(argv[2]);
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){const char*t=M+s*7+r*3; if(t[0]=='-'){ns[s][r]=-1;continue;} nw[s][r]=t[0]-'0'; mv[s][r]=t[1]=='R'?1:-1; ns[s][r]=t[2]-'A';}
  long W=1<<22; unsigned char*tape=malloc(W);
  for(int n=lo0;n<=nmax;n++){
    memset(tape,0,W); long base=W/2; for(int i=0;i<n;i++)tape[base+i]=1;
    long pos=base+n,lo=base,hi=base+n-1; long zeros=0; int st=1; long long k=0; long res=-2;
    while(1){
      int r=tape[pos]; int q=ns[st][r]; if(q<0){res=-1;break;}
      if(pos<lo){lo=pos; if(r==0)zeros++;} if(pos>hi){hi=pos; if(r==0)zeros++;}
      int w=nw[st][r]; if(r==0&&w==1)zeros--; if(r==1&&w==0)zeros++;
      tape[pos]=w; pos+=mv[st][r]; st=q; k++;
      if(st==1&&pos==hi+1&&zeros==0){res=hi-lo+1;break;}
      if(pos<2||pos>W-2){res=-3;break;}
    }
    if(res==-1)printf("%d H %lld\n",n,k); else printf("%d %ld %lld\n",n,res,k);
  }
}
