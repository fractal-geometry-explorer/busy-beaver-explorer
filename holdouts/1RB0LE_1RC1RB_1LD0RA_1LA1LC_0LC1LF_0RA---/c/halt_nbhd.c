// halt_nbhd MACHINE STEPS STATE SYMBOL: how often the head is in STATE on SYMBOL, by the three cells to its left
// (nearest first). Plain simulator; used for the near-miss count before the halting shape 1 1 1 D> 0.
#include <stdio.h>
#include <stdlib.h>
#define N (1<<24)
unsigned char tape[N]; int nx[6][2],wr[6][2],mv[6][2];
int main(int argc,char**argv){char*m=argv[1]; long long S=atoll(argv[2]); int q=argv[3][0]-'A', sym=atoi(argv[4]);
 for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*p=m+s*7+b*3; if(p[2]=='-'){nx[s][b]=-1;continue;} wr[s][b]=p[0]-'0'; mv[s][b]=p[1]=='R'?1:-1; nx[s][b]=p[2]-'A';}
 long pos=N/2; int s=0; long long cnt[8]={0};
 for(long long t=0;t<S;t++){int b=tape[pos];
  if(s==q&&b==sym){int k=tape[pos-1]*4+tape[pos-2]*2+tape[pos-3]; cnt[k]++;}
  if(nx[s][b]<0){printf("HALT %lld\n",t);break;}
  tape[pos]=wr[s][b]; pos+=mv[s][b]; s=nx[s][b];}
 for(int k=0;k<8;k++)printf("left %d%d%d : %lld\n",k>>2&1,k>>1&1,k&1,cnt[k]);}
