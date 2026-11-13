// turns MACHINE A B: plain simulation from blank tape; prints the tape (head as <S>) at every reversal of the head
// between steps A and B.
#include <stdio.h>
#include <stdlib.h>
#define N (1<<22)
unsigned char t[N];
int main(int argc,char**argv){
  const char*M=argv[1]; long long a=atoll(argv[2]),b=atoll(argv[3]);
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){const char*p=M+s*7+r*3; if(p[2]=='-'){ns[s][r]=-1;continue;} nw[s][r]=p[0]-'0';mv[s][r]=p[1]=='R'?1:-1;ns[s][r]=p[2]-'A';}
  long long h=N/2,lo=h,hi=h; int s=0,ld=0;
  for(long long st=0;st<b;st++){
    int r=t[h]; if(ns[s][r]<0){printf("halt %lld\n",st);return 0;}
    t[h]=nw[s][r]; int d=mv[s][r]; h+=d; s=ns[s][r];
    if(h<lo)lo=h; if(h>hi)hi=h;
    if(d!=ld && st>=a){
      printf("%lld %c%c: ",st+1,d>0?'R':'L','A'+s);
      for(long long i=lo;i<=hi;i++){ if(i==h) printf("<%c>",'A'+s); putchar('0'+t[i]); }
      printf("\n");
    }
    ld=d;
  }
}
