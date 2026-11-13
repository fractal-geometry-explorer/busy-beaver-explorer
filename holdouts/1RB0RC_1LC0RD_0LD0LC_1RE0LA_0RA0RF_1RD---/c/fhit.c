// fhit MACHINE STEPS MAXLINES: print step and tape (context 40 cells) each time state F (or STATE argv4) is entered
#include <stdio.h>
#include <stdlib.h>
#define N (1<<24)
unsigned char tape[N];
int main(int argc,char**argv){
  char*m=argv[1]; long long steps=atoll(argv[2]); long maxl=atol(argv[3]); int want=argc>4?argv[4][0]-'A':5;
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*t=m+s*7+r*3; if(t[0]=='-'){ns[s][r]=-1;continue;} nw[s][r]=t[0]-'0'; mv[s][r]=t[1]=='R'?1:-1; ns[s][r]=t[2]-'A';}
  long pos=N/2,lo=pos,hi=pos; int st=0; long lines=0; long long cnt=0;
  for(long long i=0;i<steps;i++){
    int r=tape[pos]; int n=ns[st][r]; if(n<0){printf("HALT %lld\n",i+1);return 0;}
    int prev=st;
    tape[pos]=nw[st][r]; pos+=mv[st][r]; st=n;
    if(pos<lo)lo=pos; if(pos>hi)hi=pos;
    if(st==want){ cnt++; if(lines<maxl){ lines++;
      printf("%lld from %c%d pos-lo=%ld hi-pos=%ld : ",i+1,'A'+prev,r,pos-lo,hi-pos);
      for(long p=pos-30;p<=pos+30;p++){ if(p<lo||p>hi){putchar(' ');continue;} if(p==pos)putchar('>'); putchar('0'+tape[p]);} putchar('\n');}}
  }
  printf("count %lld\n",cnt);
  return 0;}
