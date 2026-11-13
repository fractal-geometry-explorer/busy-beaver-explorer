// round: plain simulation of a fixed number of steps from a given tape (to check the symbolic rounds of py/closure).
// usage: round MACHINE STEPS < input     input: line 1 = state letter, line 2 = cells from the head rightwards
// (everything else blank).  Output: "HALT n" or "state head-offset first-one-offset cells" where the offsets are
// relative to the start cell and cells run from the first to the last 1.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int nw[6][2],mv[6][2],ns[6][2];
int main(int c,char**v){
  char*m=v[1];long long max=atoll(v[2]);
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*t=m+7*s+3*r; if(t[2]=='-'){ns[s][r]=-1;continue;} nw[s][r]=t[0]-'0';mv[s][r]=t[1]=='R'?1:-1;ns[s][r]=t[2]-'A';}
  char stc[8]; if(scanf("%7s",stc)!=1)return 1;
  size_t cap=1<<26; char*in=malloc(cap); if(scanf("%67108000s",in)!=1)return 1;
  long long len=strlen(in), N=8*len+4000000, org=N/4;
  unsigned char*tape=calloc(N,1);
  for(long long i=0;i<len;i++)tape[org+i]=in[i]-'0';
  long long p=org; int st=stc[0]-'A';
  for(long long k=0;k<max;k++){
    int r=tape[p]; int t=ns[st][r]; if(t<0){printf("HALT %lld\n",k);return 0;}
    tape[p]=nw[st][r];p+=mv[st][r];st=t;
    if(p<2||p>N-2){printf("OUT\n");return 0;}
  }
  long long lo=0,hi=N-1; while(lo<N&&!tape[lo])lo++; while(hi>=0&&!tape[hi])hi--;
  printf("%c %lld %lld ",'A'+st,p-org,lo-org);
  for(long long i=lo;i<=hi;i++)putchar('0'+tape[i]);
  putchar('\n');
  return 0;
}
