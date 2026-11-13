// rword MACHINE STEPS : at turns into A after a straight run >= 30 whose left side is exactly 0^inf 1110 (111110)^n 1,
// print "step n W" where W is the right side read in pairs 1b -> bit b, with runs (010)^k (k>=2) written as <k>.
// A pair not starting with 1 is printed as '?'.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<27)
unsigned char tape[N];
long lo,hi;
static int cell(long p){ return (p<lo||p>hi)?0:tape[p]; }
int main(int argc,char**argv){
  char*m=argv[1]; long long steps=atoll(argv[2]);
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*t=m+s*7+r*3; if(t[0]=='-'){ns[s][r]=-1;continue;} nw[s][r]=t[0]-'0'; mv[s][r]=t[1]=='R'?1:-1; ns[s][r]=t[2]-'A';}
  long pos=N/2,lastturn=pos,prevpos=pos; int st=0,dir=1; lo=hi=pos;
  static char bits[1<<26];
  for(long long i=0;i<steps;i++){
    int r=tape[pos]; int n=ns[st][r]; if(n<0){printf("HALT %lld\n",i+1);return 0;}
    tape[pos]=nw[st][r]; pos+=mv[st][r]; st=n;
    if(pos<lo)lo=pos; if(pos>hi)hi=pos;
    if(pos<=8||pos>=N-8){printf("OUT\n");return 0;}
    int nd=pos>prevpos?1:-1;
    if(nd!=dir){ long len=labs(prevpos-lastturn);
      if(len>=30 && st==0 && cell(pos-1)==1){
        long p=pos-2,k=0; static const char W[7]="011111";
        while(1){int ok=1;for(int j=0;j<6;j++)if(cell(p-j)!=W[j]-'0'){ok=0;break;} if(!ok)break; p-=6;k++;}
        if(cell(p)==0&&cell(p-1)==1&&cell(p-2)==1&&cell(p-3)==1&&p-3==lo){
          long nb=0; long q=pos; int bad=0;
          while(q<=hi){ if(cell(q)==1){bits[nb++]='0'+cell(q+1);} else {bits[nb++]='?';bad=1;} q+=2; }
          printf("%lld %ld ",i+1,k);
          for(long j=0;j<nb;){ long c=0; while(j+3*(c+1)<=nb&&bits[j+3*c]=='0'&&bits[j+3*c+1]=='1'&&bits[j+3*c+2]=='0')c++;
            if(c>=2){printf("<%ld>",c);j+=3*c;} else {putchar(bits[j]);j++;} }
          putchar('\n');
        }
      }
      lastturn=prevpos; dir=nd; }
    prevpos=pos;
  }
  return 0;}
