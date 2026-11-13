// plain.cpp: cell-by-cell Turing machine simulation (no acceleration), used as ground truth.
// usage: plain MACHINE MAXSTEPS [MINB] < input
// input lines:  "blank"   or   "B T"  (start = state A on the first cell of  01001000 (01)^B T , T may be "-")
// For each line: runs until the first step > 0 at which the configuration is a "node candidate"
//   (state A, every cell left of the head blank, cells from the head on read 01001000...) with B >= MINB,
//   printing "NODE steps B T" for every candidate met;  or prints "HALT steps" (steps executed before the
//   undefined transition is met)  or "LIMIT".
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#include <iostream>
#include <sstream>
int W[6][2],M[6][2],NX[6][2];
int main(int argc,char**argv){
  const char*spec=argv[1]; long long maxs=atoll(argv[2]); long long minB=argc>3?atoll(argv[3]):0;
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*p=spec+s*7+b*3; if(p[0]=='-'){NX[s][b]=-1;}else{W[s][b]=p[0]-'0';M[s][b]=p[1]=='R'?1:-1;NX[s][b]=p[2]-'A';}}
  std::string line;
  while(std::getline(std::cin,line)){
    if(line.empty()) continue;
    std::string cells;
    if(line!="blank"){ std::istringstream is(line); long long B; std::string T; is>>B>>T; if(T=="-")T="";
      cells="01001000"; for(long long i=0;i<B;i++) cells+="01"; cells+=T; }
    long long LM=4000000, N=LM+(long long)cells.size()*4+16000000;
    std::vector<unsigned char> tv(N,0); unsigned char*t=tv.data();
    for(size_t i=0;i<cells.size();i++) t[LM+i]=cells[i]-'0';
    long long p=LM; int st=0; long long step=0; const char*res="LIMIT";
    const unsigned long long PAT=(1ull<<8)|(1ull<<32);
    for(;step<maxs;){
      if(st==0 && step>0){ unsigned long long v; memcpy(&v,t+p,8);
        if(v==PAT && memchr(t,1,p)==nullptr){
          long long q=p+8, B=0; while(t[q]==0&&t[q+1]==1){B++;q+=2;}
          long long hi=N-1; while(hi>=q&&!t[hi])hi--;
          std::string T; for(long long i=q;i<=hi;i++)T+=(char)('0'+t[i]); if(T.empty())T="-";
          printf("NODE %lld %lld %s\n",step,B,T.c_str());
          if(B>=minB){res=nullptr;break;}
        } }
      int r=t[p]; int n=NX[st][r]; if(n<0){ printf("HALT %lld\n",step); res=nullptr; break; }
      t[p]=W[st][r]; p+=M[st][r]; st=n; step++;
      if(p<16||p>N-16){res="OUT";break;}
    }
    if(res) printf("%s\n",res);
    fflush(stdout);
  }
}
