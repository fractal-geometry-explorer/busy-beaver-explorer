// One half-phase of 1RB0RF_1LC---_1LF1LD_1RE0LD_0RC0RE_1LC1RA by direct simulation.  Input lines "TAPE STATE" (STATE 0 = A,
// 5 = F): the tape is the visited region, the head just right of it.  Runs until the head is again right of the
// visited region in state A or F with the tape = w (u)^k, |w| <= 24, u = 10 or 01, k larger than at the start, and
// prints "steps state w=.. u=.. k=..", or HALT / LONG.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
const char*M="1RB0RF_1LC---_1LF1LD_1RE0LD_0RC0RE_1LC1RA";
int W[8][2],Mv[8][2],Q[8][2],H[8][2];
static char t[1<<25];
int main(){
 for(int q=0;q<6;q++)for(int b=0;b<2;b++){const char*s=M+7*q+3*b;H[q][b]=(s[2]=='-');if(!H[q][b]){W[q][b]=s[0]-'0';Mv[q][b]=s[1]=='R'?1:-1;Q[q][b]=s[2]-'A';}}
 static char buf[1<<24]; int q;
 while(scanf("%s %d",buf,&q)==2){
  long N=1<<25, off=1<<20; memset(t,0,N); long len=strlen(buf); for(long i=0;i<len;i++)t[off+i]=buf[i]-'0';
  long lo=off, hi=off+len-1, pos=off+len; long long st=0; int done=0; long kprev=len/2;
  while(st<20000000000LL){
   if(pos>hi){ hi=pos;
     if((q==0||q==5)){ // check pattern
       // find lo: first 1
       long a=lo; while(a<=hi && !t[a]) a++;
       // count trailing (u)^k from hi-1 backwards? the head cell hi is blank (just entered)
       long e=hi-1; // last cell
       // try u = t[e-1]t[e]
       int u0=t[e-1],u1=t[e]; if(u0!=u1){ long j=e; long k=0; while(j-1>=a && t[j-1]==u0 && t[j]==u1){k++; j-=2;}
         if(st>0 && k>=4 && (j-a+1)<=24 && k>kprev){ printf("%lld %c w=",st,'A'+q); for(long i=a;i<=j;i++)putchar('0'+t[i]); printf(" u=%d%d k=%ld\n",u0,u1,k); fflush(stdout); done=1; break;}}
     }
   }
   if(pos<lo) lo=pos;
   int b=t[pos]; if(H[q][b]){printf("HALT %lld\n",st+1);fflush(stdout);done=1;break;} t[pos]=W[q][b]; pos+=Mv[q][b]; q=Q[q][b]; st++;
  }
  if(!done){printf("LONG\n");fflush(stdout);}
 }
}
