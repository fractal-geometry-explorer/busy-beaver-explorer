// m6c MACHINE M J STEPS [K]: start from 0^inf (1011)^M 1^(J-1) (10)^3 A> 1 0^inf (the phase start P M (J-1)); print the next K phase starts as m and j (j = n + 1 for m > 0, j = n - 1 for m = 0), or HALT
#include <stdio.h>
#include <stdlib.h>
#define N (1<<26)
unsigned char tape[N];
int main(int argc,char**argv){
  char*m=argv[1]; long M=atol(argv[2]), J=atol(argv[3]); long long steps=atoll(argv[4]); int maxp=argc>5?atoi(argv[5]):3;
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*t=m+s*7+r*3; if(t[0]=='-'){ns[s][r]=-1;continue;} nw[s][r]=t[0]-'0'; mv[s][r]=t[1]=='R'?1:-1; ns[s][r]=t[2]-'A';}
  long p=N/4; long lo=p;
  for(long i=0;i<M;i++){tape[p++]=1;tape[p++]=0;tape[p++]=1;tape[p++]=1;}
  for(long i=0;i<J;i++)tape[p++]=1;
  tape[p++]=0;tape[p++]=1;tape[p++]=0;tape[p++]=1;tape[p++]=0;
  long pos=p; tape[p]=1; long hi=p; int st=0; int found=0;
  for(long long i=0;i<steps;i++){
    int r=tape[pos]; int n=ns[st][r]; if(n<0){printf("HALT after %lld steps, pos-lo=%ld hi-pos=%ld state %c\n",i+1,pos-lo,hi-pos,'A'+st);return 0;}
    tape[pos]=nw[st][r]; pos+=mv[st][r]; st=n;
    if(pos<lo)lo=pos; if(pos>hi)hi=pos;
    if(i>0 && st==0 && pos-lo>12 && pos==hi && tape[pos]==1 && tape[pos-1]==0&&tape[pos-2]==1&&tape[pos-3]==0&&tape[pos-4]==1&&tape[pos-5]==0&&tape[pos-6]==1){
      long q=pos-6; long n1=0; while(q>=lo && tape[q]==1){n1++;q--;}
      long mm=0; while(q-1>=lo && tape[q]==0 && tape[q-1]==1 && tape[q+1]==1&&tape[q+2]==1){mm++;q-=4;}
      long extra=q-lo+1; // cells left of the (1011) groups
      if(n1<3)continue; printf("%lld m=%ld j=%ld extra=%ld\n",i+1,mm,n1-2,extra); fflush(stdout);
      if(++found>=maxp)return 0;
    }
  }
  printf("no event in %lld steps\n",steps);
  return 0;}
