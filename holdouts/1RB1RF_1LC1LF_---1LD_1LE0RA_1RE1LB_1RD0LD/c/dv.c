// The run from blank tape seen at the visits of the left end.
// usage: dv MACHINE MAXSTEPS STATE
//   each time the head reaches a new leftmost cell in STATE, prints the step count and the tape as the lengths of
//   its runs of 1s (single 0s between runs, run-length coded: "0 3 2^13 3^10 1 0 3^5 1").
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc,char**argv){
  const char*m=argv[1]; double mx=atof(argv[2]); int want=argv[3][0]-'A';
  int W[6][2],Mv[6][2],Nx[6][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*t=m+s*7+b*3; if(t[0]=='-'){Nx[s][b]=-1;continue;} W[s][b]=t[0]-'0';Mv[s][b]=t[1]=='R'?1:-1;Nx[s][b]=t[2]-'A';}
  long N=1L<<28; unsigned char*tape=calloc(N,1); long pos=N-(1L<<24),L=pos,R=pos; int st=0; unsigned long long steps=0;
  while(steps<mx){
    int b=tape[pos]; int nx=Nx[st][b]; if(nx<0){printf("HALT %llu state %c pos %ld (L=%ld R=%ld)\n",steps+1,'A'+st,pos-L,L,R);return 0;}
    tape[pos]=W[st][b]; pos+=Mv[st][b]; st=nx; steps++;
    if(pos>R)R=pos;
    if(pos<L){L=pos; if(st==want){
      printf("%llu",steps);
      long i=L; long prev=-1,cnt=0;
      while(i<=R){ long j=i; while(j<=R&&tape[j])j++; long len=j-i; 
        if(len==prev)cnt++; else { if(cnt){ if(cnt>1)printf(" %ld^%ld",prev,cnt); else printf(" %ld",prev);} prev=len;cnt=1;}
        i=j+1; }
      if(cnt){ if(cnt>1)printf(" %ld^%ld",prev,cnt); else printf(" %ld",prev);}
      printf("\n");
    }}
  }
  return 0;}
