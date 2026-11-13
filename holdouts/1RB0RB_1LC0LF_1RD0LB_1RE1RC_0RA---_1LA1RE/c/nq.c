// The next bouncer configuration Q(x',y') = 0^inf 1^x' 0 (10)^y' A> after Q(x,y) (or HALT), for y0 <= y < y1.
// usage: gcc -O2 -o nq nq.c && ./nq MACHINE x y0 y1 [maxsteps]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int W[6][2],D[6][2],S[6][2];
int main(int argc,char**argv){
  char*m=argv[1]; for(int i=0;i<6;i++)for(int r=0;r<2;r++){char*t=m+7*i+3*r; if(t[2]=='-'){S[i][r]=-1;continue;} W[i][r]=t[0]-'0';D[i][r]=t[1]=='R'?1:-1;S[i][r]=t[2]-'A';}
  int x=atoi(argv[2]),y0=atoi(argv[3]),y1=atoi(argv[4]); long long maxs=argc>5?atoll(argv[5]):4000000000LL;
  for(int y=y0;y<y1;y++){
    long L=x+1+2*y; long N=16*L+100000; unsigned char*t=calloc(N,1); long off=N/2-L;
    for(long i=0;i<x;i++)t[off+i]=1; for(long i=0;i<y;i++){t[off+x+1+2*i]=1;}
    long h=off+L,lo=off,hi=h; int st=0; long long n=0; int done=0;
    while(n<maxs){
      int r=t[h]; if(S[st][r]<0){printf("%d HALT %lld\n",y,n);done=1;break;}
      t[h]=W[st][r]; h+=D[st][r]; st=S[st][r]; n++;
      if(h<lo){lo=h; if(h<2){printf("%d OUT\n",y);done=1;break;}}
      if(h>hi){hi=h; if(h>=N-2){printf("%d OUT\n",y);done=1;break;}
        if(st==0){ // check form
          long i=lo; while(i<h&&t[i]==0)i++; long a=i; while(i<h&&t[i]==1)i++; long xx=i-a;
          if(i<h&&t[i]==0){ i++; long yy=0; int ok=1; while(i<h){ if(i+1<h&&t[i]==1&&t[i+1]==0){yy++;i+=2;} else {ok=0;break;} }
            if(ok){printf("%d Q %ld %ld %lld\n",y,xx,yy,n);done=1;break;} }
        }
      }
    }
    if(!done)printf("%d TIMEOUT\n",y);
    free(t);
  }
}
