// sim MACHINE MAXSTEPS [MODE]: plain simulation from blank tape; prints the tape, with (010)^k written [k] and the head
// as <S>, whenever the head reaches a new leftmost (MODE 1), rightmost (MODE 2) or either (MODE 0) cell.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<24)
unsigned char t[N];
int main(int argc,char**argv){
  const char*M=argv[1]; long long maxs=atoll(argv[2]); int mode=argc>3?atoi(argv[3]):0;
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){const char*p=M+s*7+r*3; if(p[2]=='-'){ns[s][r]=-1;continue;} nw[s][r]=p[0]-'0';mv[s][r]=p[1]=='R'?1:-1;ns[s][r]=p[2]-'A';}
  long long h=N/2,lo=h,hi=h; int s=0;
  for(long long st=0;st<maxs;st++){
    int r=t[h]; if(ns[s][r]<0){printf("halt %lld\n",st);return 0;}
    t[h]=nw[s][r]; h+=mv[s][r]; s=ns[s][r];
    int ev=0; if(h<lo){lo=h;ev=1;} if(h>hi){hi=h;ev=2;}
    if(ev&&(mode==0||mode==ev)){
      printf("%lld %c%c ",st+1,ev==1?'L':'R','A'+s);
      // compress: print run of chars from lo to hi, (010)^k as [k], head position marked
      long long i=lo; 
      while(i<=hi){
        if(i==h){printf("<%c>",'A'+s);}
        long long k=0; while(i+3*k+2<=hi && t[i+3*k]==0&&t[i+3*k+1]==1&&t[i+3*k+2]==0 && !(h>=i&&h<i+3*k+3&&h!=i) ) k++;
        if(k>=2){printf("[%lld]",k); i+=3*k;} else {printf("%d",t[i]); i++;}
      }
      printf("\n");
    }
  }
  printf("timeout\n");
}
