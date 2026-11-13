// Epoch starts: print the turns where the head has crossed more than FRAC of the tape since its last turn, at most one
// per 30% growth of the step count.  usage: epochs MACHINE STEPS FRAC   (e.g. ... 10000000000 0.8)
#include <stdio.h>
#include <stdlib.h>
int main(int argc,char**argv){
  char*M=argv[1]; long long N=atoll(argv[2]); double fr=atof(argv[3]);
  int wr[8][2],mv[8][2],nx[8][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*t=M+s*7+b*3; if(t[2]=='-'){nx[s][b]=-1;continue;} wr[s][b]=t[0]-'0'; mv[s][b]=t[1]=='R'?1:-1; nx[s][b]=t[2]-'A';}
  long SZ=1<<26; unsigned char*tape=calloc(SZ,1); long p=SZ/2,lo=p,hi=p,last=p; int s=0,dir=0; long long lastp=1;
  for(long long i=0;i<N;i++){int b=tape[p]; if(nx[s][b]<0){printf("HALT %lld\n",i+1);return 0;}
    tape[p]=wr[s][b]; int d=mv[s][b];
    if(d!=dir){ if(labs(p-last)>fr*(hi-lo+1)){ if(i-lastp>0.3*lastp) printf("%lld %c pos=%ld from=%ld L=%ld R=%ld\n",i,'A'+s,p-SZ/2,last-SZ/2,SZ/2-lo,hi-SZ/2); lastp=i;} last=p; dir=d;}
    p+=d; s=nx[s][b]; if(p<lo)lo=p; if(p>hi)hi=p;}
}
