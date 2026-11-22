// nextrec N R TAIL [K [MAXSTEPS]]: from 0^inf B> 0 0 1 (1100)^N (10110110)^R TAIL 0^inf run the plain machine and print the
// first K records at the left end of the form  B> 0 0 1 (1100)^n (10110110)^m T  with n >= 1 and m >= 1 or T starting
// with 1001 or 101110 (the clean records: a phase end, a new phase, or a new tail), as "n m steps T"; HALT or TIMEOUT.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define SZ (1L<<27)
static unsigned char t[SZ];
int main(int argc,char**argv){
  const char*mm="1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA";
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){const char*x=mm+s*7+r*3; if(x[0]=='-'){ns[s][r]=-1;continue;} nw[s][r]=x[0]-'0'; mv[s][r]=x[1]=='R'?1:-1; ns[s][r]=x[2]-'A';}
  long n=atol(argv[1]), m=atol(argv[2]); const char*T=argv[3]; int K=argc>4?atoi(argv[4]):1; long long MAX=argc>5?atoll(argv[5]):4000000000LL;
  long p=SZ/2,q=p; t[q++]=0;t[q++]=0;t[q++]=1;
  for(long i=0;i<n;i++){t[q++]=1;t[q++]=1;t[q++]=0;t[q++]=0;} for(long i=0;i<m;i++){const char*d="10110110";for(int k=0;k<8;k++)t[q++]=d[k]-'0';}
  for(const char*c=T;*c;c++) t[q++]=*c-'0';
  long hi=q-1, lo=p; int st=1; long long steps=0; int cnt=0;
  while(steps<MAX){
    int r=t[p]; int nx=ns[st][r]; if(nx<0){printf("HALT %lld\n",steps);return 0;}
    t[p]=nw[st][r]; p+=mv[st][r]; st=nx; steps++;
    if(p>hi){hi=p; if(hi>SZ-10){puts("OUT");return 1;}}
    if(p<lo){ lo=p; if(p<10){puts("OUTL");return 1;}
      if(st==1 && t[p]==0&&t[p+1]==0&&t[p+2]==1){
        long i=p+3,nn=0; while(t[i]==1&&t[i+1]==1&&t[i+2]==0&&t[i+3]==0){nn++;i+=4;}
        long md=0; static const unsigned char D[8]={1,0,1,1,0,1,1,0};
        while(!memcmp(t+i,D,8)){md++;i+=8;}
        int ok = nn>=1 && (md>0 || (t[i]==1&&t[i+1]==0&&t[i+2]==0&&t[i+3]==1) || (t[i]==1&&t[i+1]==0&&t[i+2]==1&&t[i+3]==1&&t[i+4]==1&&t[i+5]==0));
        if(ok){ long e=hi; while(e>i&&!t[e])e--; printf("%ld %ld %lld ",nn,md,steps);
          long j=i; if(t[j]==1&&t[j+1]==0){ printf("10 "); j+=2; long k=0; while(j+3<=e&&t[j]==1&&t[j+1]==1&&t[j+2]==1&&t[j+3]==0){k++;j+=4;} printf("(1110)^%ld ",k);} 
          for(long k=j;k<=e;k++)putchar('0'+t[k]); putchar(10); if(++cnt>=K) return 0; } } }
  }
  puts("TIMEOUT"); return 0; }
