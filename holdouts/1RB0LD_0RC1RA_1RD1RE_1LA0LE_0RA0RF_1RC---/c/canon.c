#include <stdio.h>
#include <stdlib.h>
#include <string.h>
// Plain simulator for 1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---.  usage: canon MAXSTEPS
// At each configuration  L 1^n (01)^m C> 0^inf  (state C at the right end, a 1 left of the head) with n < 3,
// and at the next such configuration after it, prints "step n m | L" (L run-length coded).
static const char *M="1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---";
int W[6][2],D[6][2],N[6][2];
int main(int argc,char**argv){
  long long maxs=atoll(argv[1]); int SZ=1<<24; unsigned char*t=calloc(SZ,1); long h=SZ/2,hi=h; int q=0;
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){const char*g=M+7*s+3*r; if(g[2]=='-'){N[s][r]=-1;continue;} W[s][r]=g[0]-'0';D[s][r]=g[1]=='R'?1:-1;N[s][r]=g[2]-'A';}
  long hi1=h; int flag=0; // max index with a 1
  for(long long st=0;st<maxs;st++){
    if(q==2 && h>hi1 && t[h-1]){
      long i=h-1,m=0; while(t[i]==1 && t[i-1]==0){m++; i-=2;}
      long n=0; while(t[i]==1){n++; i--;}
      if(n<3||flag){ flag=(n<3); printf("%lld n %ld m %ld | ",st,n,m);
        // print rest RLE from left
        long j=0; for(j=0;j<=i && j<SZ;j++) if(t[j]) break; if(j>i){printf("-");} else {
        long a=j; int c=t[a]; long run=0; int cnt=0;
        for(long k=a;k<=i;k++){ if(t[k]==c) run++; else { printf("%d^%ld ",c,run); c=t[k]; run=1; if(++cnt>60){printf("...");break;} } }
        if(cnt<=60) printf("%d^%ld",c,run); }
        printf("\n"); fflush(stdout);
      }
    }
    int r=t[h]; if(N[q][r]<0){printf("HALT %lld\n",st);return 0;}
    t[h]=W[q][r]; if(t[h]&&h>hi1)hi1=h; if(!t[h]&&h==hi1){while(hi1>0&&!t[hi1])hi1--;}
    h+=D[q][r]; q=N[q][r]; if(h<3||h>=SZ-1){printf("OUT\n");return 0;}
  }
}
