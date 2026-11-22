// One wall visit per input line, by direct simulation.  A line is the cells (0/1) to the right of the wall cell;
// the head starts in F on the wall cell (a 0, blank tape to its left).  Output per line:
//   H steps pos E<s> t     the visit halts (pos: the cell read by the halting E, wall = 0)
//   V steps pos cells E<s> t   the next wall visit (F on a 0 at a new leftmost cell pos, wall = 0) and the cells
//                         to its right (pos = -2 for an ordinary visit)
//   T steps E<s> t         no result within the cap
// E<s> t: the state in which the head first went past the last input cell, at step t (- if never: no event).
// usage: visit [cap] < lines
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static const char*M="1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA";
int W[6][2],Mv[6][2],Nx[6][2];
int main(int argc,char**argv){
 long cap=argc>1?atol(argv[1]):10000000;
 for(int s=0;s<6;s++)for(int r=0;r<2;r++){const char*q=M+s*7+r*3; if(q[0]=='-')Nx[s][r]=-1; else {W[s][r]=q[0]-'0';Mv[s][r]=q[1]=='R'?1:-1;Nx[s][r]=q[2]-'A';}}
 static char line[1<<20]; long SZ=1L<<24; char*t=malloc(SZ);
 while(fgets(line,sizeof line,stdin)){
  int L=strlen(line); while(L&&(line[L-1]==10||line[L-1]==13))line[--L]=0;
  memset(t,0,SZ); long base=SZ/2; long p=base; for(int i=0;i<L;i++)t[base+1+i]=line[i]-'0';
  long hi0=base+L; long lo=p,hi=hi0; int s=5; long n=0; char ev='-'; long evstep=0; int res=0;
  while(n<cap){ int r=t[p]; if(Nx[s][r]<0){res=1;break;}
    t[p]=W[s][r]; p+=Mv[s][r]; s=Nx[s][r]; n++;
    if(p>hi){hi=p; if(ev=='-'&&p>hi0+0){ev='A'+s;evstep=n;}}
    if(p<lo){lo=p; if(s==5&&t[p]==0){res=2;break;}}
    if(p<=0||p>=SZ-1){res=3;break;}
  }
  if(res==1){printf("H %ld %ld E%c %ld\n",n+1,p-base,ev,evstep);}
  else if(res==2){ long h=hi; while(h>p&&t[h]==0)h--; printf("V %ld %ld ",n,p-base); for(long i=p+1;i<=h;i++)putchar('0'+t[i]); printf(" E%c %ld\n",ev,evstep);}
  else printf("T %ld E%c %ld\n",n,ev,evstep);
  fflush(stdout);
 }
}
