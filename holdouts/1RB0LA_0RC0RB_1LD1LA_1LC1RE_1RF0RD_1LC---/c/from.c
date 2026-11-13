// from MACHINE TAPE MAXSTEPS STATE SIDE [K]: TAPE like 0011S0101 where S (a state letter A-F) marks the head, on the
// cell right after it.  Prints "STEPS tape" (tape from leftmost to rightmost nonzero cell or head, head marked by its
// state letter before the cell) each time the head in STATE is at the SIDE end of the visited cells, at most K
// times (K = 0: print nothing, and the final tape at the end); then "halted STEPS" / "running STEPS".
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int nx[6][2],wr[6][2],mv[6][2];
int main(int argc,char**argv){
  char*m=argv[1]; char*tp=argv[2]; long long N=atoll(argv[3]); int S=argv[4][0]-'A'; int side=argv[5][0]=='R';
  long long K=argc>6?atoll(argv[6]):1000000;
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*t=m+s*7+b*3; if(t[2]=='-'){nx[s][b]=-1;continue;} wr[s][b]=t[0]-'0'; mv[s][b]=t[1]=='R'?1:-1; nx[s][b]=t[2]-'A';}
  long long SZ=1<<26; unsigned char*T=calloc(SZ,1); long long h=SZ/2; int st=0;
  long long L=strlen(tp), p=SZ/2, hp=-1;
  for(long long i=0;i<L;i++){ if(tp[i]>='A'&&tp[i]<='F'){hp=p;st=tp[i]-'A';} else T[p++]=tp[i]-'0'; }
  h=hp; long long lo=SZ/2, hi=p-1; if(h>hi)hi=h;
  long long cnt=0;
  for(long long k=1;k<=N;k++){
    int b=T[h]; int ns=nx[st][b]; if(ns<0){printf("halted %lld\n",k);return 0;}
    T[h]=wr[st][b]; h+=mv[st][b]; st=ns; if(h<lo)lo=h; if(h>hi)hi=h;
    if(h<=1||h>=SZ-2){printf("tape %lld\n",k);return 1;}
    if(K&&st==S&&h==(side?hi:lo)){
      long long a=lo,z=hi; while(a<h&&!T[a])a++; while(z>h&&!T[z])z--;
      printf("%lld ",k);
      for(long long i=a;i<=z;i++){ if(i==h)putchar('A'+st); putchar('0'+T[i]); }
      putchar('\n');
      if(++cnt>=K){printf("running %lld\n",k);return 0;}
    }
  }
  if(!K){ long long a=lo,z=hi; while(a<h&&!T[a])a++; while(z>h&&!T[z])z--; printf("%lld ",N); for(long long i=a;i<=z;i++){ if(i==h)putchar('A'+st); putchar('0'+T[i]); } putchar('\n'); }
  printf("running %lld\n",N);
  return 0;
}
