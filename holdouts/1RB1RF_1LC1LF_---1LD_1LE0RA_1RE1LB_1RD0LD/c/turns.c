// turns MACHINE MAXSTEPS FROM [MIND]: the plain machine from blank tape; from step FROM on, prints the tape (run lengths,
// the head as [cells of its run left of it]) at every turn of the head after a move of at least MIND cells (default 6).
#include <stdio.h>
#include <stdlib.h>
int main(int argc,char**argv){
  const char*m=argv[1]; unsigned long long mx=atof(argv[2]), from=atof(argv[3]); long mind=argc>4?atol(argv[4]):6;
  int W[6][2],Mv[6][2],Nx[6][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*t=m+s*7+b*3; if(t[0]=='-'){Nx[s][b]=-1;continue;} W[s][b]=t[0]-'0';Mv[s][b]=t[1]=='R'?1:-1;Nx[s][b]=t[2]-'A';}
  long N=1L<<26; unsigned char*tape=calloc(N,1); long pos=N-(1L<<22),L=pos,R=pos; int st=0; unsigned long long steps=0; int lastmv=1; long lastturn=pos;
  while(steps<mx){
    int b=tape[pos]; int nx=Nx[st][b]; if(nx<0){printf("HALT\n");return 0;}
    int mv=Mv[st][b]; tape[pos]=W[st][b];
    if(mv!=lastmv){ long d=pos-lastturn; if(d<0)d=-d; if(d>=mind && steps>=from){
      // print tape as runs with head marker
      printf("%llu %c%c ",steps,"ABCDEF"[nx],mv>0?'>':'<'); long c=0,prev=-1,cnt=0; 
      for(long i=L;i<=R+1;i++){ if(i==pos)printf(" [%ld]",c); if(tape[i])c++; else { if(c==prev)cnt++; else { if(cnt){ if(cnt>1)printf(" %ld^%ld",prev,cnt); else printf(" %ld",prev);} prev=c;cnt=1;} c=0; if(i==pos){ if(cnt){ if(cnt>1)printf(" %ld^%ld",prev,cnt); else printf(" %ld",prev);} prev=-1;cnt=0; } } }
      if(cnt){ if(cnt>1)printf(" %ld^%ld",prev,cnt); else printf(" %ld",prev);} printf("\n"); }
      lastturn=pos; }
    lastmv=mv; pos+=mv; st=nx; steps++;
    if(pos>R)R=pos; if(pos<L)L=pos;
  }
}
