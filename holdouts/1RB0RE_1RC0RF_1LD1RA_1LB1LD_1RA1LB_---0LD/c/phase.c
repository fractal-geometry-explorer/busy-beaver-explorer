// One phase of 1RB0RE_1RC0RF_1LD1RA_1LB1LD_1RA1LB_---0LD by direct simulation.  Input lines "X TAIL": the start
// 0^inf B> 0 1 0^X TAIL 0^inf.  Runs until the head is in B on the cell just left of the leftmost 1, the tape being
// 1 0^X' TAIL' with X' > X; prints "steps X' TAIL'" (TAIL' up to its last 1), or HALT / LONG.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
const char*M="1RB0RE_1RC0RF_1LD1RA_1LB1LD_1RA1LB_---0LD";
int W[8][2],Mv[8][2],Q[8][2],H[8][2];
static char t[1<<26];
int main(){
 for(int q=0;q<6;q++)for(int b=0;b<2;b++){const char*s=M+7*q+3*b;H[q][b]=(s[2]=='-');if(!H[q][b]){W[q][b]=s[0]-'0';Mv[q][b]=s[1]=='R'?1:-1;Q[q][b]=s[2]-'A';}}
 static char tail[1<<20]; long X;
 while(scanf("%ld %s",&X,tail)==2){
  long N=1<<26, off=1<<24; memset(t,0,N);
  long tl=strlen(tail); if(tail[0]=='-') tl=0;
  t[off]=1; for(long i=0;i<tl;i++) t[off+1+X+i]=tail[i]-'0';
  long pos=off-1; int q=1; long long st=0; int done=0;
  while(st<40000000000LL){
   int b=t[pos]; if(H[q][b]){printf("HALT %lld\n",st+1);done=1;break;}
   t[pos]=W[q][b]; pos+=Mv[q][b]; q=Q[q][b]; st++;
   if(q==1 && t[pos]==0 && t[pos+1]==1){
     // leftmost 1?
     long a=pos+1; int ok=1; for(long i=a-1;i>=a-64 && i>=0;i--) if(t[i]){ok=0;break;}
     if(ok){ long j=a+1; while(j<N && !t[j]) j++; long Xp=j-a-1;
       if(4*Xp>5*X && j<N-1){ long e=N-1; // last 1
         long last=j; for(long i=j;i<j+4000000 && i<N;i++) if(t[i]) last=i;
         printf("%lld %ld ",st,Xp); for(long i=j;i<=last;i++)putchar('0'+t[i]); putchar('\n'); fflush(stdout); done=1; break; } } }
  }
  if(!done){printf("LONG\n");fflush(stdout);}
 }
}
