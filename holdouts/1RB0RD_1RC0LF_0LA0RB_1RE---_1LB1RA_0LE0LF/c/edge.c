// edge MAXCYCLES [PRINTEVERY] [LIST]: the "edge machine" of 1RB0RD_1RC0LF_0LA0RB_1RE---_1LB1RA_0LE0LF, exact.
//
// From step 2035 on the tape is   0^inf (1001111)^n 0100 111111 a b | data,   the cut `|` between cells 12 and 13
// (cell 0 = the start cell).  Z(n, R) is the configuration with a b = 0 1, the head on cell 13 in state E and the
// data R to the right.  The machine is run step by step; whenever the head comes to cell 12
// from the right in state B or F and reads 1 with a 1 on cell 11, Lean theorems `wall_cycle_B` / `wall_cycle_F`
// (lean/Rules.lean) say that 168(n-1)+575 steps later the configuration is Z(n+3, R): six sweeps of the wall and
// the head back at the cut.  That jump is taken here in one go.  The run stops with an error if the head ever comes
// to cell 4 (the wall would be touched in a way the theorems do not cover).
//
// Prints each cycle at which the data grows, and every PRINTEVERY cycles: cycle, n, step count at Z, data length,
// deepest cell of the cycle [, data if LIST].  Step counts are those of the plain machine from blank tape.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
#define N (1<<20)
static unsigned char t[N];
static void p128(u128 v){ char b[50]; int i=49; b[i]=0; if(!v)b[--i]='0'; while(v){b[--i]='0'+(int)(v%10); v/=10;} fputs(b+i,stdout); }
int main(int argc,char**argv){
  const char*m="1RB0RD_1RC0LF_0LA0RB_1RE---_1LB1RA_0LE0LF";
  long long maxc=argc>1?atoll(argv[1]):1000; long long every=argc>2?atoll(argv[2]):0; int list=argc>3;
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){const char*p=m+s*7+r*3; if(p[0]=='-'){ns[s][r]=-1;continue;} nw[s][r]=p[0]-'0'; mv[s][r]=p[1]=='R'?1:-1; ns[s][r]=p[2]-'A';}
  // Z(7, 01010000010010001001) at step 2035 (lean: `reach_Z`)
  const char*left="0100111111" "01"; for(int i=0;i<12;i++) t[1+i]=left[i]-'0';
  const char*d0="01010000010010001001"; long hi=12; for(int i=0;d0[i];i++){ t[13+i]=d0[i]-'0'; hi=13+i; }
  u128 steps=2035; long long n=7, c=0; long pos=13; int st=4; long deep=13; long long local=0;
  for(;;){
    int r=t[pos]; int q=ns[st][r];
    if(q<0){ printf("HALT in cycle %lld at step ",c); p128(steps+local+1); printf("\n"); return 0; }
    t[pos]=nw[st][r]; int d=mv[st][r]; pos+=d; st=q; local++;
    if(pos>deep){ deep=pos; if(pos>hi){ hi=pos; if(hi>=N-2){printf("overflow\n");return 1;} } }
    if(pos==12 && d<0 && (st==1||st==5) && t[12]==1 && t[11]==1){
      int grew = 0; static long lasthi=0; if(hi!=lasthi){grew=1;lasthi=hi;}
      steps+=local; local=0; steps+=(u128)168*(n-1)+575; n+=3; c++;
      t[11]=0; t[12]=1; pos=13; st=4;
      if(grew || (every && c%every==0) || c>=maxc){
        printf("%s %lld n %lld step ",grew?"grow ":"cycle",c,n); p128(steps); printf(" data %ld deep %ld",hi-12,deep);
        if(list){ putchar(' '); for(long p=13;p<=hi;p++) putchar('0'+t[p]); }
        putchar('\n'); fflush(stdout); }
      if(c>=maxc) return 0;
      deep=13;
    } else if(pos<=4){ printf("UNEXPECTED: head at cell 4 in cycle %lld\n",c); return 2; }
  }
}
