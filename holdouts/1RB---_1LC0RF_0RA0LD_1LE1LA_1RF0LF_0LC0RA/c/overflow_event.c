// The overflow event of 1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA, cell by cell.
// Reads lines "LEFT RIGHT" (cells; the head in state A on RIGHT[0], the event cell) and runs the machine. Every time
// the head is in state A on a 0 with the left part 0^inf 1 0 (100|110|010)* (a full event) it prints
//   EV steps position LEFT RIGHT        (RIGHT from the head's cell on)
// and goes on; it prints HALT steps position state if the machine halts, MAX steps at the step limit.
// py/overflow_jump.py reads the output and stops it at the first full event in the layered layout.
// usage: gcc -O2 -o overflow_event holdouts/1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA/c/overflow_event.c; ./overflow_event MAXSTEPS
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int W[6][2],Mv[6][2],Nx[6][2];
static char L[1<<22],R[1<<22];
int main(int argc,char**argv){
  char*m="1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA"; long long maxs=atoll(argv[1]);
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*t=m+7*s+3*r; if(t[2]=='-'){Nx[s][r]=-1;continue;} W[s][r]=t[0]-'0';Mv[s][r]=t[1]=='R'?1:-1;Nx[s][r]=t[2]-'A';}
  while(scanf("%s %s",L,R)==2){
    long long N=strlen(L)+strlen(R)+(1<<21); unsigned char*tp=calloc(N+(1<<21),1); long long off=1<<20;
    long long nl=strlen(L),nr=strlen(R);
    for(long long i=0;i<nl;i++)tp[off-nl+i]=L[i]-'0';
    for(long long i=0;i<nr;i++)tp[off+i]=R[i]-'0';
    long long p=off,lo=off-nl,hi=off+nr; int st=0; long long k=0; int done=0;
    while(k<maxs){
      int r=tp[p]; int nx=Nx[st][r]; if(nx<0){printf("HALT %lld %lld %d\n",k,p-off,st);done=1;break;}
      tp[p]=W[st][r]; p+=Mv[st][r]; st=nx; k++; if(p<lo)lo=p; if(p>hi)hi=p;
      if(p<16||p>N+(1<<21)-16){printf("RANGE\n");done=1;break;}
      if(st==0&&tp[p]==0&&tp[p-1]==0){
        // check left: from p-1 go left in 3-cell digits until we hit 0 1 (i.e. "10" then zeros)
        long long q=p; int ok=1;
        while(1){ if(q-3<lo-2){ok=0;break;}
          int a=tp[q-3],b=tp[q-2],c=tp[q-1];
          if(c==0&&((a==1&&b==0)||(a==1&&b==1)||(a==0&&b==1))){
            // could also be the 1 0 end: check if q-2..q-1 == 1 0 and everything left is 0
            if(tp[q-2]==1&&tp[q-1]==0){ long long j=q-3; int z=1; for(;j>=lo-1;j--) if(tp[j]){z=0;break;} if(z){break;} }
            q-=3; continue; }
          if(tp[q-2]==1&&tp[q-1]==0){ long long j=q-3; int z=1; for(;j>=lo-1;j--) if(tp[j]){z=0;break;} if(z)break; }
          ok=0;break; }
        if(ok){ printf("EV %lld %lld ",k,p-off); for(long long i=lo;i<p;i++)putchar('0'+tp[i]); putchar(' '); for(long long i=p;i<=hi;i++)putchar('0'+tp[i]); putchar('\n'); fflush(stdout); }
      }
    }
    if(!done)printf("MAX %lld\n",k);
    fflush(stdout); free(tp);
  }
}
