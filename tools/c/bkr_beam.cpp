// bkr_beam.cpp: search for one long backward chain from a halting stencil (beam of K random stencils per depth).
// Prints CHAIN depth D state head window: a finite tape window from which the machine runs exactly D steps and halts
// without leaving the window. Its existence shows backward reasoning (busycoq BackwardsReasoning.v) fails at every depth <= D.
// Usage: ./bkr_beam MACHINE D K SEED
// beam search for a long backward chain: keep up to K random distinct stencils per depth (window stored as vector<char>)
#include <bits/stdc++.h>
using namespace std;
struct S { string t; int h; int q; bool operator<(const S&o)const{ return tie(q,h,t)<tie(o.q,o.h,o.t);} bool operator==(const S&o)const{return q==o.q&&h==o.h&&t==o.t;} };
int ns, W[8][2], Dm[8][2], N[8][2];
int main(int argc,char**argv){
  string m=argv[1]; int D=atoi(argv[2]); size_t K=atoll(argv[3]); mt19937_64 rng(atoi(argv[4]));
  vector<string> parts; {string t; for(char c:m){ if(c=='_'){parts.push_back(t);t="";} else t+=c;} parts.push_back(t);}
  ns=parts.size();
  for(int q=0;q<ns;q++)for(int s=0;s<2;s++){ string t=parts[q].substr(3*s,3); if(t[2]=='-'){N[q][s]=-1;continue;} W[q][s]=t[0]-'0'; Dm[q][s]=t[1]=='R'?1:-1; N[q][s]=t[2]-'A'; }
  vector<S> cur; for(int q=0;q<ns;q++)for(int s=0;s<2;s++) if(N[q][s]<0) cur.push_back({string(1,'0'+s),0,q});
  for(int d=1; d<=D; d++){
    vector<S> nx;
    for(auto&st:cur) for(int p=0;p<ns;p++)for(int s=0;s<2;s++){
      if(N[p][s]!=st.q) continue; int w=W[p][s]; int hp=st.h-Dm[p][s]; S y=st; y.q=p;
      if(hp<0){ y.t.insert(y.t.begin(),'0'+s); y.h=0; }
      else if(hp>=(int)st.t.size()){ y.t.push_back('0'+s); y.h=hp; }
      else { if(st.t[hp]-'0'!=w) continue; y.t[hp]='0'+s; y.h=hp; }
      nx.push_back(y);
    }
    sort(nx.begin(),nx.end()); nx.erase(unique(nx.begin(),nx.end()),nx.end());
    if(nx.empty()){ printf("beam died at depth %d (inconclusive)\n",d); return 0;}
    if(nx.size()>K){ shuffle(nx.begin(),nx.end(),rng); nx.resize(K);} 
    if(d%250==0){ printf("depth %d kept %zu\n",d,nx.size()); fflush(stdout);} 
    cur.swap(nx);
  }
  auto &x=cur[0]; printf("CHAIN depth %d state %c head %d window %s\n",D,'A'+x.q,x.h,x.t.c_str());
}
