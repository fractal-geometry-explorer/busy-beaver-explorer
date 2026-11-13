// machine 14: print the tape at refill moments (head A at left end, tape 1 0 1 1 0 0 ...), as tokens
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define SZ (1<<26)
static unsigned char t[SZ];
int main(int argc,char**argv){
  long long N=(long long)atof(argv[1]); int maxw=argc>2?atoi(argv[2]):400;
  // A0 1RB A1 0LE B0 1LC B1 0RA C0 1LD C1 0RC D0 1LE D1 1LF E0 1LA E1 0LC F0 0LA F1 halt
  int W[6][2]={{1,0},{1,0},{1,0},{1,1},{1,0},{0,-1}};
  int Mv[6][2]={{1,-1},{-1,1},{-1,1},{-1,-1},{-1,-1},{-1,0}};
  int Nx[6][2]={{1,4},{2,0},{3,2},{4,5},{0,2},{0,-1}};
  long long p=SZ/2,lo=p,hi=p; int s=0;
  for(long long n=0;n<N;n++){
    int r=t[p];
    if(p==lo&&s==0&&r==1&&t[p+1]==0&&t[p+2]==1&&t[p+3]==1&&t[p+4]==0&&t[p+5]==0){
      printf("%lld",n);
      long long i=p; int w=0;
      while(i<=hi && w<maxw){
        if(t[i]==1&&i+1<=hi&&t[i+1]==0){long long j=i;while(j+1<=hi&&t[j]==1&&t[j+1]==0)j+=2; printf(" %lld",(j-i)/2); i=j;}
        else {printf(" %c",t[i]?'!':'.'); i++;}
        w++;
      }
      printf("\n"); fflush(stdout);
    }
    if(s==5&&r==1){printf("halt %lld\n",n);return 0;}
    int nw=W[s][r],mv=Mv[s][r],ns=Nx[s][r];
    t[p]=nw; p+=mv; s=ns; if(p<lo)lo=p; if(p>hi)hi=p;
    if(p<=0||p>=SZ-1){printf("out of tape %lld\n",n);return 1;}
  }
  printf("end %lld\n",N);
}
