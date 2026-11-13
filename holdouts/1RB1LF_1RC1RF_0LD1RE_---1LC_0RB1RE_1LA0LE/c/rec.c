// Records printer: at each new cell on SIDE in one of STATES, print the step and the tape run-length coded.
// usage: rec MACHINE MAXSTEPS L|R STATES|* MAXTOKENS [EVERY]   (gcc -O2 -o rec rec.c)
// rec MACHINE MAXSTEPS SIDE(L/R) STATES(e.g. A or ABC or *) MAXTOK [EVERY]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int W[6][2],Mv[6][2],Nx[6][2];
int main(int argc,char**argv){
  char*m=argv[1]; long long max=atoll(argv[2]); char side=argv[3][0]; char*sts=argv[4]; int maxtok=atoi(argv[5]);
  long long every=argc>6?atoll(argv[6]):1;
  for(int i=0;i<6;i++)for(int s=0;s<2;s++){char*t=m+7*i+3*s; if(t[2]=='-'){Nx[i][s]=-1;continue;} W[i][s]=t[0]-'0';Mv[i][s]=t[1]=='R'?1:-1;Nx[i][s]=t[2]-'A';}
  int N=1<<24; unsigned char*tp=calloc(N,1); long long pos=N/2,lo=pos,hi=pos; int st=0; long long cnt=0;
  for(long long k=0;k<max;k++){
    int s=tp[pos]; int nx=Nx[st][s]; if(nx<0){printf("HALT %lld\n",k+1);return 0;}
    tp[pos]=W[st][s]; pos+=Mv[st][s]; st=nx;
    if(pos<=1||pos>=N-2){printf("OUT\n");return 0;}
    int rec=0;
    if(pos<lo){lo=pos; if(side=='L')rec=1;}
    if(pos>hi){hi=pos; if(side=='R')rec=1;}
    if(rec && (sts[0]=='*'||strchr(sts,'A'+st))){
      cnt++; if(cnt%every) continue;
      printf("%lld",k+1);
      int ntok=0; long long x;
      long long a=lo,b=hi;
      if(side=='L'){ for(x=a;x<=b&&ntok<maxtok;){ if(x==pos){printf(" %c>%d",'A'+st,tp[x]);x++;ntok++;continue;} long long y=x; while(y<=b&&y!=pos&&tp[y]==tp[x])y++; if(y-x>1)printf(" %d^%lld",tp[x],y-x); else printf(" %d",tp[x]); x=y; ntok++;} }
      else { // print from right end backwards, then reverse? print last maxtok tokens: collect
        long long start=b; int t=0; long long x2=b;
        while(x2>=a && t<maxtok){ if(x2==pos){x2--;t++;continue;} long long y=x2; while(y>=a&&y!=pos&&tp[y]==tp[x2])y--; x2=y; t++; }
        if(x2>=a) printf(" ...");
        for(x=x2+1;x<=b;){ if(x==pos){printf(" %c>%d",'A'+st,tp[x]);x++;continue;} long long y=x; while(y<=b&&y!=pos&&tp[y]==tp[x])y++; if(y-x>1)printf(" %d^%lld",tp[x],y-x); else printf(" %d",tp[x]); x=y;}
      }
      printf("\n");
    }
  }
  printf("MAX\n");
}
