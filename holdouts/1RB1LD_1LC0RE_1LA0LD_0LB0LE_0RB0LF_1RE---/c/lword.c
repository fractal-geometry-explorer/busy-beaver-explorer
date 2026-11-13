// lword MACHINE STEPS : for 1RB1LD_1LC0RE_1LA0LD_0LB0LE_0RB0LF_1RE---. At turns into E after a straight run >= 30 where
// the tape is  [left] 1 0 1 0 0 E> 0 (1110)^y 111111 0^inf, print "step y W": W = the left part read from the head
// outwards (right to left) cell by cell, up to its last 1; runs (0001)^k (k>=2) are written <k>.
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
      if(len>=30 && st==4){
        long p=pos; int ok=cell(p)==0; p++; long y=0;
        while(ok&&cell(p)==1&&cell(p+1)==1&&cell(p+2)==1&&cell(p+3)==0){p+=4;y++;}
        for(int j=0;j<6&&ok;j++) if(cell(p+j)!=1) ok=0;
        p+=6; while(ok&&p<=hi){ if(cell(p))ok=0; p++; }
        static const int H[5]={1,0,1,0,0};
        for(int j=0;j<5&&ok;j++) if(cell(pos-5+j)!=H[j]) ok=0;
        if(ok){
          long q=pos-6; long nb=0; long first=lo; while(first<q&&cell(first)==0) first++;
          while(q>=first){ bits[nb++]='0'+cell(q); q--; }
          printf("%lld %ld ",i+1,y);
          for(long j=0;j<nb;){ long c=0; while(j+4*(c+1)<=nb&&bits[j+4*c]=='0'&&bits[j+4*c+1]=='0'&&bits[j+4*c+2]=='0'&&bits[j+4*c+3]=='1')c++;
            if(c>=2){printf("<%ld>",c);j+=4*c;} else {putchar(bits[j]);j++;} }
          putchar('\n');
        }
      }
      lastturn=prevpos; dir=nd; }
    prevpos=pos;
  }
  return 0;}
