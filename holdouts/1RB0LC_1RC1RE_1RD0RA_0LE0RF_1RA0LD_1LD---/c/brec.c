// The run of a machine read as sweeps: at every B-record (the head reaches a new cell on the right in state B)
// count it; print the tape as digits every K-th one, and every one where the left end moved or the right end is in
// its other phase (`1^4 B>0`).  Output: steps, record number, leftmost cell, then `r<len>` (leftmost block),
// `d*n` (n digits d in a row, a digit d being a block 0 1^(3d+2); -1000-len for a block that is not a digit) and
// `|e<len>` (the ones before the head).
// usage: brec MACHINE MAX_STEPS K   (gcc -O2 -o brec brec.c)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int W[6][2],Mv[6][2],Nx[6][2];
int main(int argc,char**argv){
  char*m=argv[1]; long long N=atoll(argv[2]); long long K=atoll(argv[3]); int stB = argc>4? argv[4][0]-'A':1;
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*g=m+7*s+3*b; if(g[2]=='-'){Nx[s][b]=-1;continue;} W[s][b]=g[0]-'0';Mv[s][b]=g[1]=='R'?1:-1;Nx[s][b]=g[2]-'A';}
  long long SZ=1LL<<30; unsigned char*t=calloc(SZ,1); long long p=SZ/2,lo=p,hi=p; int s=0; long long rec=0;
  for(long long n=0;n<N;n++){
    int b=t[p]; int nx=Nx[s][b]; if(nx<0){printf("HALT %lld\n",n+1);return 0;}
    t[p]=W[s][b]; p+=Mv[s][b]; s=nx;
    if(p<lo)lo=p;
    if(p>hi){hi=p; if(s==stB){rec++; static long long plo=0; int ev = (t[p-2]==1) || lo!=plo; plo=lo; if(rec%K==0 || ev){
      printf("%lld %lld %lld :",n+1,rec,lo-SZ/2);
      long long i=lo; while(t[i]==0&&i<p)i++;
      // blocks
      long long prevd=-99,cnt=0; int first=1;
      while(i<p){ long long j=i; while(j<p&&t[j]==1)j++; long long len=j-i;
        if(j>=p){ if(cnt) printf(" %lld*%lld",prevd,cnt); printf(" |e%lld",len); break;}
        if(first){printf(" r%lld",len);first=0;}
        else { long long d = (len-2)%3==0? (len-2)/3 : -1000-len;
          if(d==prevd)cnt++; else { if(cnt) printf(" %lld*%lld",prevd,cnt); prevd=d;cnt=1;} }
        i=j+1; }
      printf("\n"); fflush(stdout);
    }}}
  }
  return 0;
}
