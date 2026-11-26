// Robustness test: at sweep R0 the words between the prefix `111 x x z` and the last KEEP words are replaced by a
// random word of L words x, y, z (probabilities px, py, rest z); then the run continues to STEPS and a halt is reported.
// usage: randw MACHINE STEPS R0 L px py KEEP SEED
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define T (1<<24)
static unsigned char tape[T], tmp[T];
int main(int argc,char**argv){
  char*m=argv[1]; long long N=atoll(argv[2]); int R0=atoi(argv[3]); int L=atoi(argv[4]); double px=atof(argv[5]),py=atof(argv[6]); int KEEP=atoi(argv[7]); srand(atoi(argv[8]));
  int w[6][2],d[6][2],n[6][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*x=m+7*s+3*b; if(x[0]=='-'){n[s][b]=-1;continue;} w[s][b]=x[0]-'0'; d[s][b]=x[1]=='R'?1:-1; n[s][b]=x[2]-'A';}
  long p=T/2,lo=p,hi=p; int s=0; int last=0; long round=0;
  for(long long i=0;i<N;i++){int b=tape[p]; if(n[s][b]<0){printf("HALT step %lld round %ld\n",i,round);return 0;} tape[p]=w[s][b]; p+=d[s][b]; s=n[s][b];
    if(p>hi){hi=p; if(last!=1){ last=1; round++;
      if(round==R0){
        long q=lo; while(tape[q]==0)q++; long st=q; while(tape[q]==1)q++; // ones
        // skip 3 words (x x z)
        for(int k=0;k<3;k++){ while(tape[q]==0)q++; while(tape[q]==1)q++; }
        long a=q;
        // find start of last KEEP words: scan words, record starts
        static long ws[1<<20]; int nw=0; long r=q;
        while(r<=hi){ long s0=r; while(r<=hi&&tape[r]==0)r++; if(r>hi)break; while(r<=hi&&tape[r]==1)r++; ws[nw++]=s0; }
        long bpos=ws[nw-KEEP];
        long len=hi+1-bpos; memcpy(tmp,tape+bpos,len+64);
        long o=a;
        for(int k=0;k<L;k++){ double u=rand()/(double)RAND_MAX; const char*t= u<px? "0001": u<px+py? "0001111":"0111111"; for(int j=0;t[j];j++) tape[o++]=t[j]-'0'; }
        long shift=o-bpos; memcpy(tape+o,tmp,len+64); p+=shift; hi+=shift;
        for(long z=hi+64; z<hi+100000 && z<T; z++) tape[z]=0;
      }
    }}
    if(p<lo){lo=p; last=-1;}
    if(p<2||p>T-3){printf("OUT round %ld\n",round);return 0;}
  }
  printf("nohalt round %ld\n",round); return 0;}
