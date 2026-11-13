// m3depth: the reduced run of m3red.c that also prints, at the end, a histogram of the carry depth: how many cells at
// the left end of the tape right of the x block changed from one record in B to the next.  usage: m3depth K ROUNDS PRINTEVERY
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N 4096
unsigned char tape[N];
int main(int argc,char**argv){
  const char*m="1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC";
  int K=atoi(argv[1]); long long R=atoll(argv[2]); long long PE=atoll(argv[3]);
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){const char*t=m+s*7+r*3; if(t[0]=='-'){ns[s][r]=-1;continue;} nw[s][r]=t[0]-'0'; mv[s][r]=t[1]=='R'?1:-1; ns[s][r]=t[2]-'A';}
  long pos=N/2,lo=pos,hi=pos; int st=0; long long rounds=0; long long steps=0; long long removed=0; long hi0=-1; long long lastg=-1;
  while(rounds<R){
    int r=tape[pos]; int n=ns[st][r]; if(n<0){printf("HALT round %lld steps %lld removed %lld\n",rounds,steps,removed);return 0;}
    tape[pos]=nw[st][r]; pos+=mv[st][r]; st=n; steps++;
    if(pos>hi){hi=pos; if(hi0>=0 && lastg!=rounds){lastg=rounds; printf("RIGHT GROWS round %lld steps %lld width %ld\n",rounds,steps,hi-lo);}}
    if(pos<lo){lo=pos;
      if(st==1){ // B record
        rounds++;
        if(rounds==1000) hi0=hi;
        // tape: pos is the new 0 cell; then 1 0 then (1011)^n
        long p=pos+1;
        if(!(tape[p]==1&&tape[p+1]==0)){printf("bad shape round %lld\n",rounds);return 1;}
        p+=2; int cnt=0; while(tape[p]==1&&tape[p+1]==0&&tape[p+2]==1&&tape[p+3]==1){cnt++;p+=4;}
        { static unsigned char prev[4096]; static long plen=0; static long long hist[300]; long len=hi-p+1; long k=0; if(plen>0){ while(k<len && k<plen && prev[plen-1-k]==tape[hi-k]) k++; long d=len-k; if(d<300) hist[d]++; } memcpy(prev,tape+p,len); plen=len; if(rounds==R-1){ for(int i=0;i<300;i++) if(hist[i]) printf("depth %d %lld\n",i,hist[i]); } }
        if(PE && rounds%PE==0){printf("%lld %lld n=%d T=",rounds,steps,cnt); for(long q=p;q<=hi;q++)putchar('0'+tape[q]); putchar('\n');}
        if(cnt>K+1){ int d=((cnt-K)/2)*8; // remove d cells after pos+2: shift cells [pos .. pos+2] right by d
          memmove(tape+pos+d,tape+pos,3); memset(tape+pos,0,d); pos+=d; lo=pos; removed+=((cnt-K)/2)*2; }
      }
    }
    if(pos<=2||pos>=N-2){printf("OUT\n");return 0;}
  }
  printf("done rounds %lld steps %lld\n",rounds,steps);
  return 0;}
