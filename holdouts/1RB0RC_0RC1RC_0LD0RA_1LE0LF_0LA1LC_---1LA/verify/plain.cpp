// plain cell-by-cell simulator, prints tape snapshots when head is at leftmost-ever / on demand
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>
#include <string>
typedef unsigned long long u64;
int main(int argc,char**argv){
  const char* spec="1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA";
  int W[6][2],M[6][2],N[6][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*p=spec+s*7+b*3; if(p[0]=='-'){N[s][b]=-1;W[s][b]=1;M[s][b]=1;}else{W[s][b]=p[0]-'0';M[s][b]=p[1]=='R'?1:-1;N[s][b]=p[2]-'A';}}
  u64 T=strtoull(argv[1],0,10); int mode=argc>2?atoi(argv[2]):0;
  size_t SZ=1<<26; std::vector<unsigned char> t(SZ,0); long pos=SZ/2; long lo=pos,hi=pos; int s=0; u64 n=0;
  if(argc>4){ s=argv[3][0]-'A'; const char*q=argv[4]; for(long i=0;q[i];i++){ t[pos+i]=q[i]-'0'; hi=pos+i; } }
  auto dump=[&](){ printf("%llu %c pos=%ld lo=%ld : ",n,'A'+s,pos-lo,lo-(long)SZ/2); for(long i=lo;i<=hi;i++){ if(i==pos)putchar('['); putchar('0'+t[i]); if(i==pos)putchar(']');} putchar('\n'); };
  while(n<T){
    int b=t[pos]; if(N[s][b]<0){printf("HALT at step %llu (+1)\n",n);break;}
    t[pos]=W[s][b]; int m=M[s][b]; s=N[s][b]; pos+=m; n++;
    if(pos<lo){lo=pos; if(mode==1)dump();}
    if(pos>hi){hi=pos; if(mode==2)dump();}
  }
  if(mode==0||mode==3)dump();
  return 0;
}
