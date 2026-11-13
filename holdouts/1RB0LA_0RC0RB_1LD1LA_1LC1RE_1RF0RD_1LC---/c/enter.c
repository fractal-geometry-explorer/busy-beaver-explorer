// enter: log each time head (state B after A0, or E after D1 not preceded by E1) is on a 1 starting a run of 1s that
// reaches the rightmost 1 with length>=TH.  prints: steps state context | runlength
#include <stdio.h>
#include <stdlib.h>
int nx[6][2],wr[6][2],mv[6][2];
int main(int argc,char**argv){
  char*m=argv[1]; long long N=atoll(argv[2]); int TH=argc>3?atoi(argv[3]):10; int CL=argc>4?atoi(argv[4]):80;
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*t=m+s*7+b*3; if(t[2]=='-'){nx[s][b]=-1;continue;} wr[s][b]=t[0]-'0'; mv[s][b]=t[1]=='R'?1:-1; nx[s][b]=t[2]-'A';}
  long long SZ=1<<25; unsigned char*T=calloc(SZ,1); long long h=SZ/2, lo=h, hi=h; int st=0;
  int p1=-1,p2=-1; // previous transitions (state*2+read)
  for(long long k=1;k<=N;k++){
    int b=T[h]; int ns=nx[st][b]; if(ns<0){printf("HALT %lld\n",k);return 0;}
    T[h]=wr[st][b]; h+=mv[st][b]; p2=p1; p1=st*2+b; st=ns; if(h<lo)lo=h; if(h>hi)hi=h;
    if(h<=1||h>=SZ-2){fprintf(stderr,"tape\n");return 1;}
    if(T[h]&&((st==1&&p1==0)||(st==4&&p1==7&&p2!=9))){
      long long r=h; while(r<=hi&&T[r])r++;
      long long q=r; while(q<=hi&&!T[q])q++;
      if(q>hi && r-h>=TH){
        printf("%lld %c ",k,'A'+st);
        long long a=lo; while(a<h&&!T[a])a++;
        if(h-a>CL) a=h-CL;
        for(long long i=a;i<h;i++)putchar('0'+T[i]);
        printf(" | %lld\n",r-h);
      }
    }
  }
  return 0;
}
