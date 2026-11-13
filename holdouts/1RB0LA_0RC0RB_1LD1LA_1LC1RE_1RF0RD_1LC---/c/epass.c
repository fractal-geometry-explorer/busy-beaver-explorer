// epass MACHINE CTX N [maxsteps]: start "CTX E> 1^N" on blank tape; run to the next E-entry event (as enter.c);
// print "ctx' n' steps" or "HALT steps" or "MAX"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int nx[6][2],wr[6][2],mv[6][2];
int main(int argc,char**argv){
  char*m=argv[1]; char*ctx=argv[2]; long long n=atoll(argv[3]); long long N=argc>4?atoll(argv[4]):4000000000LL;
  int TH=argc>5?atoi(argv[5]):1; char st0=argc>6?argv[6][0]:'E';
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*t=m+s*7+b*3; if(t[2]=='-'){nx[s][b]=-1;continue;} wr[s][b]=t[0]-'0'; mv[s][b]=t[1]=='R'?1:-1; nx[s][b]=t[2]-'A';}
  long long SZ=8*n+4096; unsigned char*T=calloc(SZ,1); long long h=2048, lo, hi; int st=st0-'A';
  int L=strlen(ctx); for(int i=0;i<L;i++)T[h-L+i]=ctx[i]-'0'; for(long long i=0;i<n;i++)T[h+i]=1;
  lo=h-L; hi=h+n;
  int p1=-1,p2=-1;
  for(long long k=1;k<=N;k++){
    int b=T[h]; int ns=nx[st][b]; if(ns<0){printf("HALT %lld\n",k);return 0;}
    T[h]=wr[st][b]; h+=mv[st][b]; p2=p1; p1=st*2+b; st=ns; if(h<lo)lo=h; if(h>hi)hi=h;
    if(h<=1||h>=SZ-2){printf("TAPE %lld\n",k);return 1;}
    if(st==4&&T[h]&&p1==7&&p2!=9){
      long long r=h; while(r<=hi&&T[r])r++;
      long long q=r; while(q<=hi&&!T[q])q++;
      if(q>hi && r-h>=TH){
        long long a=lo; while(a<h&&!T[a])a++;
        for(long long i=a;i<h;i++)putchar('0'+T[i]);
        printf(" %lld %lld\n",r-h,k); return 0;
      }
    }
  }
  printf("MAX\n");
  return 0;
}
