// erec: simulate a machine from blank tape; at each "E-record" (head at a new rightmost cell, state E, reading 0,
// cell to the left = 1) print "STEPS parse" where parse codes the tape lo..head-2 with S=01100, <n>=(10)^n.
// usage: erec MACHINE MAXSTEPS [EVERY]   (prints every EVERY-th record, default 1; always the last)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<26)
static unsigned char tape[N];
int tr_w[6][2],tr_d[6][2],tr_s[6][2];
static void pr(long long st,long lo,long h){
  printf("%lld ",st); long p=lo; long run=0;
  while(p<=h-2){
    if(p+4<=h-2 && tape[p]==0&&tape[p+1]==1&&tape[p+2]==1&&tape[p+3]==0&&tape[p+4]==0){ if(run){printf("<%ld>",run);run=0;} putchar('S'); p+=5; continue;}
    if(p+1<=h-2 && tape[p]==1&&tape[p+1]==0){run++;p+=2;continue;}
    if(run){printf("<%ld>",run);run=0;}
    putchar('0'+tape[p]); p++;
  }
  if(run)printf("<%ld>",run);
  printf("1[E]0\n");
}
int main(int argc,char**argv){
  const char*m=argv[1]; long long max=atoll(argv[2]); long long every=argc>3?atoll(argv[3]):1; long long from=argc>4?atoll(argv[4]):0;
  for(int i=0;i<6;i++)for(int r=0;r<2;r++){const char*g=m+7*i+3*r; if(g[0]=='-'){tr_s[i][r]=-1;continue;} tr_w[i][r]=g[0]-'0'; tr_d[i][r]=g[1]=='R'?1:-1; tr_s[i][r]=g[2]-'A';}
  long pos=N/2, lo=pos, hi=pos; int s=0; long long st=0, nrec=0;
  while(st<max){
    int c=tape[pos]; int ns=tr_s[s][c];
    if(ns<0){printf("HALT %lld\n",st+1);return 0;}
    tape[pos]=tr_w[s][c]; pos+=tr_d[s][c]; s=ns; st++;
    if(pos<lo){lo=pos; if(pos<2){fprintf(stderr,"left overflow\n");return 1;}}
    if(pos>hi){hi=pos; if(pos>N-2){fprintf(stderr,"right overflow\n");return 1;}
      if(s==4 && tape[pos]==0 && tape[pos-1]==1){ nrec++; if(nrec>=from && nrec%every==0) pr(st,lo,pos);} }
  }
  printf("END %lld\n",st);
}
