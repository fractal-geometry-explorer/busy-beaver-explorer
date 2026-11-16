// Run-length window CPS for 1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB (16 November 2026): the K nearest runs on each side,
// lengths exact below T1 (1-runs) / T0 (0-runs) and mod 3 above, runs within JL / JR of the blank end kept exact (up to TX).
// usage: g++ -O2 -std=c++17 rlwin.cpp -o rlwin && ./rlwin K T1 T0 JL TX MAXCFG JR
// Result: no closed set; every parameter set tried reaches a halt or exceeds MAXCFG (see README).
// run-length CPS with mod-3 classes; usage: rlcps K T1 T0 [maxcfg]
#include <bits/stdc++.h>
using namespace std;
int W_[6][2],D_[6][2],S_[6][2];
int K,T[2],J,TX,JS[2]; struct WinSet; WinSet*WLp; long long MAXC;
typedef string Side; // pairs of bytes (bit, cls)
const unsigned char INF=255;
// codes: 1..199 exact length; 200+r class (>=T, len%3==r); 255 INF
unsigned char inc(int b,unsigned char c,bool ex){ if(c==INF) return INF; if(c<200){ int n=c+1; if(n<T[b] || (ex && n<=TX)) return n; return 200+(n%3);} return 200+((c-200+1)%3);}
void dec(int b,unsigned char c, vector<unsigned char>&out){ out.clear(); if(c==INF){out.push_back(INF);return;} if(c<200){out.push_back(c-1);return;} int r=c-200; out.push_back(200+((r+2)%3)); if(T[b]%3==r) out.push_back(T[b]-1);}
bool hasInf(const Side&s){ return !s.empty() && (unsigned char)s[s.size()-1]==INF; }
struct WinSet { unordered_map<string, set<string>> m; long long n=0; };
Side push(const Side&s,int w,WinSet&W){
  Side n;
  int nr=s.size()/2; // runs incl INF
  if(!s.empty() && (unsigned char)s[0]==w){ bool ex=hasInf(s) && (nr-2)<JS[&W==WLp?0:1]; n=s; n[1]=(char)inc(w,(unsigned char)s[1],ex); }
  else { n.push_back((char)w); n.push_back((char)(T[w]>1?1:200+1)); n+=s; }
  if((int)n.size()>2*K){ string win=n.substr(2,2*K); string key=win.substr(0,2*(K-1)); string last=win.substr(2*(K-1),2);
    auto &st=W.m[key]; if(st.insert(last).second) W.n++; n=n.substr(0,2*K);}
  return n;
}
void pop(const Side&s,WinSet&W, vector<pair<int,Side>>&res){
  res.clear(); int b=(unsigned char)s[0]; unsigned char c=s[1]; vector<unsigned char> cs; dec(b,c,cs);
  for(auto c2:cs){ Side s2; if(c2==0) s2=s.substr(2); else { s2=s; s2[1]=(char)c2; }
    bool term = !s2.empty() && (unsigned char)s2[s2.size()-1]==INF;
    if(term || (int)s2.size()>=2*K){ res.push_back({b,s2}); continue;}
    auto it=W.m.find(s2); if(it==W.m.end()) continue;
    for(auto &nx: it->second) res.push_back({b,s2+nx});
  }
}
int main(int argc,char**argv){
  const char*TM="1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB";
  for(int i=0;i<6;i++)for(int r=0;r<2;r++){const char*g=TM+7*i+3*r; if(g[0]=='-'){S_[i][r]=-1;continue;} W_[i][r]=g[0]-'0';D_[i][r]=g[1]=='R'?1:-1;S_[i][r]=g[2]-'A';}
  K=atoi(argv[1]); T[1]=atoi(argv[2]); T[0]=atoi(argv[3]); JS[0]=atoi(argv[4]); JS[1]=atoi(argv[7]); TX=atoi(argv[5]); MAXC=atoll(argv[6]);
  WinSet WL,WR; WLp=&WL; Side blank; blank.push_back(0); blank.push_back((char)INF);
  auto key=[](int s,const Side&L,const Side&R){ string k; k.push_back((char)s); k.push_back((char)L.size()); k+=L; k+=R; return k;};
  unordered_set<string> seen; vector<tuple<int,Side,Side>> cfgs; vector<long long> par;
  seen.insert(key(0,blank,blank)); cfgs.push_back({0,blank,blank}); par.push_back(-1);
  vector<pair<int,Side>> pr, pl;
  int round=0;
  while(true){
    long long n0=WL.n,n1=WR.n; round++;
    for(size_t i=0;i<cfgs.size();i++){
      auto [s,L,R]=cfgs[i];
      pop(R,WR,pr);
      for(auto &[x,R2]:pr){
        if(S_[s][x]<0){ // halt
          printf("HALT K=%d T1=%d T0=%d cfgs=%zu round=%d\n",K,T[1],T[0],cfgs.size(),round);
          auto pside=[](const Side&q){ string o; for(size_t j=0;j<q.size();j+=2){int b=(unsigned char)q[j],c=(unsigned char)q[j+1]; o+= to_string(b)+"^"+(c==INF?string("inf"):(c>=200?string("m")+to_string(c-200):to_string(c)))+" ";} return o;};
          printf("  L: %s\n  R: %s\n", pside(L).c_str(), pside(R).c_str());
          long long j=i; FILE*f=fopen("path.txt","w"); while(j>=0){ auto [ss,LL,RR]=cfgs[j]; fprintf(f,"%c | %s| %s\n",'A'+ss,pside(LL).c_str(),pside(RR).c_str()); j=par[j];} fclose(f); return 1;}
        int w=W_[s][x],d=D_[s][x],s2=S_[s][x];
        if(d==1){ Side L2=push(L,w,WL); string k=key(s2,L2,R2); if(seen.insert(k).second) {cfgs.push_back({s2,L2,R2}); par.push_back(i);} }
        else { pop(L,WL,pl); for(auto &[y,L2]:pl){ Side R3=push(push(R2,w,WR),y,WR); string k=key(s2,L2,R3); if(seen.insert(k).second) {cfgs.push_back({s2,L2,R3}); par.push_back(i);} } }
      }
      if((long long)cfgs.size()>MAXC){ printf("BIG K=%d T1=%d T0=%d\n",K,T[1],T[0]); return 2;}
    }
    if(WL.n==n0 && WR.n==n1) break;
  }
  printf("CLOSED K=%d T1=%d T0=%d cfgs=%zu WL=%lld WR=%lld rounds=%d\n",K,T[1],T[0],cfgs.size(),WL.n,WR.n,round);
  return 0;
}
