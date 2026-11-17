// extev MACHINE STEPS MAXEV OUT: record the new-extreme events of a run (side and state byte, ones count, step).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc,char**argv){
  const char*t=argv[1]; long long N=atoll(argv[2]); long MAXEV=atol(argv[3]);
  int w[6][2],d[6][2],s[6][2];
  for(int i=0;i<6;i++)for(int y=0;y<2;y++){const char*p=t+7*i+3*y; if(p[2]=='-'){s[i][y]=-1;w[i][y]=0;d[i][y]=0;} else {w[i][y]=p[0]-'0';d[i][y]=p[1]=='R'?1:-1;s[i][y]=p[2]-'A';}}
  long long SZ=1<<24; unsigned char*tp=calloc(SZ,1); long long h=SZ/2, lo=h, hi=h; int st=0; long ones=0;
  FILE*f=fopen(argv[4],"wb"); long nev=0; long long i;
  for(i=0;i<N;i++){
    int y=tp[h]; int ns=s[st][y]; if(ns<0)break;
    ones+=w[st][y]-y; tp[h]=w[st][y]; h+=d[st][y]; st=ns;
    if(h<1||h>=SZ-1)break;
    if(h<lo||h>hi){ int side = h>hi; if(h<lo)lo=h; else hi=h;
      unsigned char b=side<<3|st; int32_t o=ones; int64_t ss=i+1;
      fwrite(&b,1,1,f); fwrite(&o,4,1,f); fwrite(&ss,8,1,f);
      if(++nev>=MAXEV)break; }
  }
  fclose(f); printf("%s %lld %ld %d\n",t,i,nev, (i<N && nev<MAXEV && !(h<1||h>=SZ-1)));
}
