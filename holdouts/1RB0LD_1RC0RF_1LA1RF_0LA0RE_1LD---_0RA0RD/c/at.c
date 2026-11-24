// Run a 6-state machine from blank tape for exactly STEPS steps and print the state, the cells left of the head
// and the cells from the head on (24 November 2026; used by py/directcheck.py).
// usage: ./at MACHINE STEPS
#include <stdio.h>
#include <stdlib.h>
#define N (1<<26)
unsigned char t[N];
int main(int argc,char**argv){
  const char*m=argv[1]; unsigned long long S=strtoull(argv[2],0,10);
  int w[6][2],mv[6][2],nx[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){const char*p=m+s*7+r*3; if(p[0]=='-'){nx[s][r]=-1;continue;} w[s][r]=p[0]-'0'; mv[s][r]=p[1]=='R'?1:-1; nx[s][r]=p[2]-'A';}
  long h=N/2,lo=h,hi=h; int s=0;
  for(unsigned long long st=0;st<S;st++){int r=t[h]; int ns=nx[s][r]; if(ns<0){printf("HALT\n");return 1;} t[h]=w[s][r]; h+=mv[s][r]; s=ns; if(h<lo)lo=h; if(h>hi)hi=h;}
  printf("%c ",'A'+s); for(long i=lo;i<h;i++) putchar('0'+t[i]); printf(" | "); for(long i=h;i<=hi;i++) putchar('0'+t[i]); putchar('\n');
}
