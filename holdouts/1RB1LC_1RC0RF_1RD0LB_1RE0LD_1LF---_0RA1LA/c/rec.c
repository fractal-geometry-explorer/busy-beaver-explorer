// rec MACHINE STEPS SIDE(L/R/B) [MAXLINES] [MINGAP]: print "step side state tape" at each new record cell on SIDE
#include <stdio.h>
#include <stdlib.h>
#define N (1<<25)
unsigned char tape[N];
int main(int argc,char**argv){
  char*m=argv[1]; long long steps=atoll(argv[2]); char S=argv[3][0]; long maxl=argc>4?atol(argv[4]):1000000; long long gap=argc>5?atoll(argv[5]):0;
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*t=m+s*7+r*3; if(t[0]=='-'){ns[s][r]=-1;continue;} nw[s][r]=t[0]-'0'; mv[s][r]=t[1]=='R'?1:-1; ns[s][r]=t[2]-'A';}
  long pos=N/2,lo=pos,hi=pos; int st=0; long lines=0; long long lastp=-gap-1;
  for(long long i=0;i<steps;i++){
    int r=tape[pos]; int n=ns[st][r]; if(n<0){printf("HALT %lld state %c pos %ld\n",i,'A'+st,pos-N/2);return 0;}
    tape[pos]=nw[st][r]; pos+=mv[st][r]; st=n;
    int side=0;
    if(pos<lo){lo=pos;side=-1;} if(pos>hi){hi=pos;side=1;}
    if(pos<=2||pos>=N-2){printf("OUT\n");return 0;}
    if(side && (S=='B' || (S=='L'&&side<0) || (S=='R'&&side>0)) && i-lastp>gap){
      lastp=i;
      printf("%lld %c %c ",i+1,side<0?'L':'R','A'+st);
      for(long p=lo;p<=hi;p++){ if(p==pos)putchar('>'); putchar('0'+tape[p]);} putchar('\n');
      if(++lines>=maxl)return 0;}
  }
  printf("END lo %ld hi %ld\n",lo-N/2,hi-N/2);
  return 0;}
