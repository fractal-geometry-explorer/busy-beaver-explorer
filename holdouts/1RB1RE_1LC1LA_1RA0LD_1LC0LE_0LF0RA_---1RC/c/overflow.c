// The plain machine started from a tape given as a run list.
// usage: overflow MACHINE MAXSTEPS < lines of run lengths
// Each input line is a tape: the lengths of its runs of 1s, left to right, single 0s between runs; the head starts in
// state A at the right end, on the second 0 after the last run (a visit of the right end).  The run goes on until the
// head steps left of the leftmost 1 (an overflow) or the machine halts.  At an overflow it prints the number of
// right-end visits and steps so far and the state in which the head left the tape (C, D: it bounces; E: it is about to
// halt), then runs on to the next right-end visit and prints the tape there as run lengths (the middle of a long
// tape is cut), or HALT.  Used by py/overflow.py.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<25)
static unsigned char t[N];
int W[6][2],D[6][2],S[6][2];
int main(int argc,char**argv){
  const char*m=argv[1]; double maxs=atof(argv[2]);
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*p=m+7*s+3*b; if(p[0]=='-'){S[s][b]=-1;continue;} W[s][b]=p[0]-'0';D[s][b]=p[1]=='R'?1:-1;S[s][b]=p[2]-'A';}
  char line[1<<20];
  while(fgets(line,sizeof line,stdin)){
    memset(t,0,N); long L0=N/8,p=L0; char*q=line; long v; int n; int first=1;
    while(sscanf(q,"%ld%n",&v,&n)==1){ if(!first)p++; first=0; for(long i=0;i<v;i++)t[p++]=1; q+=n; }
    long pos=p+1, hi=pos; int st=0; double steps=0; long visits=0; int ov=0;
    for(;;){
      if(steps>=maxs){printf("RUN visits %ld\n",visits);break;}
      int b=t[pos]; if(S[st][b]<0){printf("HALT visits %ld steps %.0f pos-L0 %ld\n",visits,steps,pos-L0);break;}
      int ns=S[st][b]; t[pos]=W[st][b]; pos+=D[st][b]; st=ns; steps++;
      if(pos<L0&&!ov){ov=1; printf("OVERFLOW visits %ld steps %.0f state %c | ",visits,steps,'A'+st);}
      if(pos>hi){hi=pos; if(st==0&&t[pos]==0&&t[pos-1]==0){visits++; if(ov){ long a=L0-3; while(!t[a])a++; long c=0; int out=0;
            for(long i=a;i<pos;i++){ if(t[i])c++; else { if(out<60||i>pos-40)printf("%ld ",c); else if(out==60)printf("... "); out++; c=0; if(!t[i+1]&&i+1<pos){} } }
            printf("\n"); break; } } }
    }
  }
}
