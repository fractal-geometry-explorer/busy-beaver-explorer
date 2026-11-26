// One phase of a "gap and tail" machine by direct simulation, cell by cell (any machine with this phase shape).
// usage: phaseend MACHINE STATE      e.g. phaseend 1RB0RE_1RC0RF_1LD1RA_1LB1LD_1RA1LB_---0LD B
// Input lines "X TAIL" (TAIL a word over 0/1, or - for the empty tail): the start is
//     0^inf STATE> 0 1 0^X TAIL 0^inf.
// Runs until the head is again in STATE on the cell just left of the leftmost 1, the tape being 1 0^X' TAIL'
// with X' > 5X/4.  Prints "DEPTH X' SHIFT TAIL'": DEPTH is the rightmost cell the head visited, counted from
// the first cell of TAIL (negative: the tail was not reached); SHIFT is the position of the first cell of TAIL'
// counted the same way.  Prints HALT if the machine halts first, LONG after 4*10^9 steps.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int W[8][2],Mv[8][2],Q[8][2],H[8][2];
static char t[1<<24];
int main(int argc,char**argv){
 if(argc<3){fprintf(stderr,"usage: phaseend MACHINE STATE\n");return 1;}
 const char*M=argv[1]; int q0=argv[2][0]-'A';
 for(int q=0;q<6;q++)for(int b=0;b<2;b++){const char*s=M+7*q+3*b;H[q][b]=(s[2]=='-');if(!H[q][b]){W[q][b]=s[0]-'0';Mv[q][b]=s[1]=='R'?1:-1;Q[q][b]=s[2]-'A';}}
 static char tail[1<<20]; long X; long N=1<<24, off=1<<22;
 while(scanf("%ld %1048575s",&X,tail)==2){
  long tl=strlen(tail); if(tail[0]=='-') tl=0;
  long need=4*X+2*tl+100000; if(need>off-64){printf("LONG\n");fflush(stdout);continue;}
  long lo=off-need, hi=off+need; memset(t+lo,0,hi-lo);
  t[off]=1; long ts=off+1+X; for(long i=0;i<tl;i++) t[ts+i]=tail[i]-'0';
  long pos=off-1; int q=q0; long long st=0; int done=0; long maxp=pos;
  while(st<4000000000LL){
   if(pos>maxp)maxp=pos;
   if(pos<=lo+64||pos>=hi-64)break;
   int b=t[pos]; if(H[q][b]){printf("HALT %ld\n",maxp-ts);fflush(stdout);done=1;break;}
   t[pos]=W[q][b]; pos+=Mv[q][b]; q=Q[q][b]; st++;
   if(q==q0 && t[pos]==0 && t[pos+1]==1){
     long a=pos+1; int ok=1; for(long i=a-1;i>=a-64;i--) if(t[i]){ok=0;break;}
     if(ok){ long j=a+1; while(j<hi && !t[j]) j++; long Xp=j-a-1;
       if(4*Xp>5*X && j<hi){ long last=j; for(long i=j;i<hi;i++) if(t[i]) last=i;
         printf("%ld %ld %ld ",maxp-ts,Xp,j-ts); for(long i=j;i<=last;i++)putchar('0'+t[i]); putchar('\n'); fflush(stdout); done=1; break; } } }
  }
  if(!done){printf("LONG\n");fflush(stdout);}
 }
 return 0;
}
