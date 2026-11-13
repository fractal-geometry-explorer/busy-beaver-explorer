// busy M steps [from]: visit counts per (cell,state) between step from and steps; print top 20
#include <stdio.h>
#include <stdlib.h>
#define N (1<<22)
unsigned char tape[N]; long long cnt[N][6];
int main(int argc,char**argv){char*m=argv[1]; long long mx=atoll(argv[2]); long long from=argc>3?atoll(argv[3]):0; int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*p=m+s*7+r*3; if(p[2]=='-'){ns[s][r]=-1;continue;} nw[s][r]=p[0]-'0'; mv[s][r]=p[1]=='R'?1:-1; ns[s][r]=p[2]-'A';}
  long pos=N/2,lo=pos,hi=pos; int st=0;
  for(long long k=0;k<mx;k++){int r=tape[pos]; int s2=ns[st][r]; if(s2<0){printf("HALT %lld\n",k+1);return 0;} if(k>=from)cnt[pos][st]++;
   tape[pos]=nw[st][r]; pos+=mv[st][r]; st=s2; if(pos<lo)lo=pos; if(pos>hi)hi=pos;}
  printf("lo %ld hi %ld\n",lo-N/2,hi-N/2);
  for(int j=0;j<25;j++){long long b=-1; long bi=0; int bs=0; for(long i=lo;i<=hi;i++)for(int s=0;s<6;s++)if(cnt[i][s]>b){b=cnt[i][s];bi=i;bs=s;}
   printf("%ld %c %lld\n",bi-N/2,'A'+bs,b); cnt[bi][bs]=-2;}
}
