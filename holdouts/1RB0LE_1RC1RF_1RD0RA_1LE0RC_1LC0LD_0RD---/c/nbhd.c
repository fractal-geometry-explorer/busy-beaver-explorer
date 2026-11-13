// nbhd MACHINE STEPS STATE SYMBOL: how often the head is in STATE on SYMBOL, by the 3 cells on each side
// (printed outward from the head: left l1 l2 l3, right r1 r2 r3). Plain simulator.
#include <stdio.h>
#include <stdlib.h>
#define N (1<<25)
unsigned char tape[N]; int nx[6][2],wr[6][2],mv[6][2]; long long cnt[64];
int main(int argc,char**argv){char*m=argv[1]; long long S=atoll(argv[2]); int q=argv[3][0]-'A', sym=atoi(argv[4]);
 for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*p=m+s*7+b*3; if(p[2]=='-'){nx[s][b]=-1;continue;} wr[s][b]=p[0]-'0'; mv[s][b]=p[1]=='R'?1:-1; nx[s][b]=p[2]-'A';}
 long pos=N/2; int s=0;
 for(long long t=0;t<S;t++){int b=tape[pos];
  if(s==q&&b==sym){int k=tape[pos-1]<<5|tape[pos-2]<<4|tape[pos-3]<<3|tape[pos+1]<<2|tape[pos+2]<<1|tape[pos+3]; cnt[k]++;}
  if(nx[s][b]<0){printf("HALT %lld\n",t);break;}
  tape[pos]=wr[s][b]; pos+=mv[s][b]; s=nx[s][b];}
 for(int k=0;k<64;k++) if(cnt[k]) printf("left %d%d%d right %d%d%d : %lld\n",k>>5&1,k>>4&1,k>>3&1,k>>2&1,k>>1&1,k&1,cnt[k]);}
