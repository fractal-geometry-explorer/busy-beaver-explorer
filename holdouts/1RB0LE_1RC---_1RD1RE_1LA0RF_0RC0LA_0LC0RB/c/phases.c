/* The tape of a two-symbol 6-state machine, compressed into repeated words, at the visits to the left end that come
   after a long absence of the head (for 1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB: the starts of its phases, and in
   a round-trip phase every left-end visit of the 4-visit cycle, whose gaps alternate by more than a factor 4).

   build:  gcc -O2 -o phases holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/c/phases.c
   usage:  ./phases MACHINE STEPS GAP
           prints  step  "after" steps-since-last-left-visit  "len" tape-length:  compressed tape
           for each new left-end cell reached more than GAP steps and more than 4 times the previous gap after the
           one before.  `(w)^k` is w repeated k times (periods up to 16, at least 3 copies). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<26)
static unsigned char tape[N];
static void rle(long lo,long hi){
  // greedy period search up to 16, min 3 reps
  long i=lo; 
  while(i<=hi){
    int bestp=0; long bestr=0;
    for(int p=1;p<=16;p++){ long r=1; while(i+(r+1)*p-1<=hi && !memcmp(tape+i,tape+i+r*p,p)) r++; if(r>=3 && r*p>bestr*bestp+p){bestp=p;bestr=r;} }
    if(bestp){ putchar('('); for(int k=0;k<bestp;k++) putchar('0'+tape[i+k]); printf(")^%ld ",bestr); i+=bestr*bestp; }
    else { putchar('0'+tape[i]); i++; if(i<=hi && 0) putchar(' '); }
  }
  putchar('\n');
}
int main(int argc,char**argv){
  const char*M=argv[1]; long long T=(long long)atof(argv[2]); if(argc<4){fprintf(stderr,"usage: phases MACHINE STEPS GAP\n");return 1;} long long gap=atoll(argv[3]);
  int W[12],D[12],S[12];
  for(int s=0;s<6;s++)for(int y=0;y<2;y++){const char*p=M+s*7+y*3;int i=s*2+y; if(p[0]=='-'){S[i]=-1;continue;} W[i]=p[0]-'0';D[i]=p[1]=='R'?1:-1;S[i]=p[2]-'A';}
  long h=N/2,lo=h,hi=h; int st=0; long long t=0,last=0,pg=0;
  while(t<T){
    int i=st*2+tape[h]; if(S[i]<0){printf("HALT %lld\n",t+1);return 0;}
    tape[h]=W[i]; h+=D[i]; st=S[i]; t++;
    if(h>hi)hi=h;
    if(h<lo){ lo=h; if(t-last>gap && t-last>4*pg){ printf("%lld after %lld len %ld: ",t,t-last,hi-lo+1); rle(lo,hi);} pg=t-last; last=t; }
    if(h<2||h>N-3){printf("full\n");return 1;}
  }
  return 0;
}
