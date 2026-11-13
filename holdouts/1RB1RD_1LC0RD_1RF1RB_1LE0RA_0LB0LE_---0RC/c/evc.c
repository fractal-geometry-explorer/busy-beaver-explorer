// evc MACHINE STATE MAXSTEPS : reads lines of block lists "a b c" from stdin; tape = 0 0 1^a 0 1^b ...; head at cell 0 in STATE
// runs until head at leftmost visited cell, in STATE, reading 0 (after >=1 step); prints blocks or "halt"/"timeout"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int W[8][2],Mv[8][2],Nx[8][2],H[8][2];
int main(int argc,char**argv){
  char*m=argv[1]; int S=argv[2][0]-'A'; long long max=atoll(argv[3]);
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*t=m+s*7+r*3; if(t[0]=='-'){H[s][r]=1;continue;} H[s][r]=0;W[s][r]=t[0]-'0';Mv[s][r]=t[1]=='R'?1:-1;Nx[s][r]=t[2]-'A';}
  static char line[1<<20];
  int N=1<<26; unsigned char*tape=malloc(N);
  while(fgets(line,sizeof line,stdin)){
    memset(tape,0,N); long long off=N/2, p=off+2; char*q=line; int first=1;
    while(1){ while(*q==' ')q++; if(*q=='\n'||!*q)break; long long a=strtoll(q,&q,10); if(!first)p++; first=0; for(long long i=0;i<a;i++)tape[p++]=1; }
    long long h=off, lo=off, hi=p; int st=S; long long n=0; int res=0;
    while(n<max){ int x=tape[h]; if(H[st][x]){res=1;break;} tape[h]=W[st][x]; h+=Mv[st][x]; st=Nx[st][x]; n++; if(h<lo)lo=h; if(h>hi)hi=h; if(h<2||h>N-3){res=3;break;}
      if(st==S&&h==lo&&tape[h]==0){res=2;break;} }
    if(res==1){printf("halt %lld\n",n+1);} else if(res!=2){printf("timeout\n");}
    else { printf("ev %lld :",n); long long i=lo+1; while(i<=hi&&tape[i]==0)i++; long long e=hi; while(e>=i&&tape[e]==0)e--; long long c=0; for(;i<=e;i++){ if(tape[i]) c++; else {printf(" %lld",c); c=0;} } printf(" %lld\n",c);}
    fflush(stdout);
  }
}
