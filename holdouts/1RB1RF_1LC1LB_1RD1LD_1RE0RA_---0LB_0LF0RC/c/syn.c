// syn MACHINE MAXSTEPS MODE < lines of initial run lists ("0 3 2^5 3^4 5 0 3^4 1": runs of 1s separated by single 0s, head in state D on the first cell (run 0 = the head's 0 cell))
// MODE q: one line per input: HALT steps / RUN ; MODE v: also print D-visits (new left records in state D)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int W[6][2],Mv[6][2],Nx[6][2];
static void pr(unsigned char*tape,long L,long R){ long i=L; long prev=-1,cnt=0;
      while(i<=R){ long j=i; while(j<=R&&tape[j])j++; long len=j-i; 
        if(len==prev)cnt++; else { if(cnt){ if(cnt>1)printf(" %ld^%ld",prev,cnt); else printf(" %ld",prev);} prev=len;cnt=1;}
        i=j+1; }
      if(cnt){ if(cnt>1)printf(" %ld^%ld",prev,cnt); else printf(" %ld",prev);}
      printf("\n");}
int main(int argc,char**argv){
  const char*m=argv[1]; double mx=atof(argv[2]); char mode=argv[3][0]; int st0=argc>4?argv[4][0]-'A':3;
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*t=m+s*7+b*3; if(t[0]=='-'){Nx[s][b]=-1;continue;} W[s][b]=t[0]-'0';Mv[s][b]=t[1]=='R'?1:-1;Nx[s][b]=t[2]-'A';}
  long N=1L<<26; unsigned char*tape=calloc(N,1); static char line[1<<20];
  while(fgets(line,sizeof line,stdin)){
    static long cl=0,cr=-1; if(cr>=cl)memset(tape+cl,0,cr-cl+1); long pos=N-(1L<<22),L=pos,R=pos; long p=pos; int first=1;
    char*tok=strtok(line," \n");
    while(tok){ long v=atol(tok),c=1; char*h=strchr(tok,'^'); if(h)c=atol(h+1);
      for(long k=0;k<c;k++){ if(!first){tape[p++]=0;} first=0; for(long i=0;i<v;i++)tape[p++]=1; }
      tok=strtok(NULL," \n"); }
    R=p-1; int st=st0; unsigned long long steps=0; int halted=0;
    while(steps<mx){
      int b=tape[pos]; int nx=Nx[st][b]; if(nx<0){halted=1;break;}
      tape[pos]=W[st][b]; pos+=Mv[st][b]; st=nx; steps++;
      if(pos>R)R=pos;
      if(pos<L){L=pos; if((mode=='v'||mode=='f')&&st==st0){ printf("%llu",steps); pr(tape,L,R); if(mode=='f'){halted=2;break;} } }
    }
    if(halted==2){} else if(halted){ printf("HALT %llu head_from_right %ld :",steps+1,R-pos); pr(tape,L,R);} else { printf("RUN %llu :",steps); if(mode!='v') pr(tape,L,R); else printf("\n"); }
    cl=L-2;cr=R+2; fflush(stdout);
  }
  return 0;}
