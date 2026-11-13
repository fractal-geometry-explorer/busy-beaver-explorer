// leftzone.c MAXSTEPS: every time E reads a 0 within 10 cells of the leftmost 1 (or beyond it): the first 12 cells from the leftmost 1 and E's offset; counts
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static const char *M="1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---";
#define N (1<<26)
static unsigned char tape[N];
static unsigned long long cnt[1<<12][16], first[1<<12][16];
int main(int argc,char**argv){
  double mx=atof(argv[1]);
  int w[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*t=M+7*s+3*b; if(t[2]=='-'){ns[s][b]=-1;continue;} w[s][b]=t[0]-'0';mv[s][b]=t[1]=='R'?1:-1;ns[s][b]=t[2]-'A';}
  long p=N/2,lo=p,hi=p; int st=0; unsigned long long k=0;
  while(k<mx){
    int b=tape[p];
    if(st==4&&b==0){ long l1=lo; while(tape[l1]==0&&l1<hi)l1++; long off=p-l1; if(off<=10&&off>=-4){ int key=0; for(int i=0;i<12;i++)key=key*2+tape[l1+i]; int o=(int)off+4; if(!cnt[key][o])first[key][o]=k; cnt[key][o]++; } }
    if(ns[st][b]<0){printf("HALT %llu\n",k);return 0;}
    tape[p]=w[st][b]; p+=mv[st][b]; st=ns[st][b]; k++;
    if(p>hi)hi=p; if(p<lo)lo=p;
  }
  for(int key=0;key<(1<<12);key++)for(int o=0;o<16;o++) if(cnt[key][o]){ for(int i=11;i>=0;i--)putchar('0'+((key>>i)&1)); printf(" Eoff %d count %llu first %llu\n",o-4,cnt[key][o],first[key][o]); }
}
