#include <stdio.h>
#include <stdlib.h>
#define N (1<<22)
unsigned char tape[N]; long long H[N/1024*0+8192][6];
int main(int argc,char**argv){
  char*m=argv[1]; long long from=atoll(argv[2]),to=atoll(argv[3]);
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*p=m+s*7+r*3; if(p[2]=='-'){ns[s][r]=-1;continue;} nw[s][r]=p[0]-'0'; mv[s][r]=p[1]=='R'?1:-1; ns[s][r]=p[2]-'A';}
  long pos=N/2; int st=0; long long t=0; int ld=0;
  while(t<to){int r=tape[pos]; int s2=ns[st][r]; if(s2<0){printf("HALT %lld\n",t+1);return 0;}
    tape[pos]=nw[st][r]; int d=mv[st][r]; pos+=d; st=s2; t++;
    if(t>=from && d!=ld){ long p=pos-N/2+4096; if(p>=0&&p<8192) H[p][st]++; } ld=d;
  }
  for(int p=0;p<8192;p++){long long s=0; for(int q=0;q<6;q++)s+=H[p][q]; if(s){printf("%d %lld :",p-4096,s); for(int q=0;q<6;q++) if(H[p][q]) printf(" %c%lld",'A'+q,H[p][q]); printf("\n");}}
}
