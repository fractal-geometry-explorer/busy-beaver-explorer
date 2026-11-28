// region closure: region = first m tokens; arrivals = carries from cstar file (state, M cells from boundary)
#include <bits/stdc++.h>
using namespace std;
int W[6][2]={{1,1},{1,1},{1,0},{9,1},{1,0},{0,1}};
int Mv[6][2]={{1,1},{1,-1},{-1,-1},{0,-1},{1,-1},{1,1}};
int Q[6][2]={{1,5},{2,2},{3,4},{9,4},{5,1},{0,4}};
int m, M; long MAXSTEPS=200000;
vector<pair<int,string>> C;
// tape as vector with offset
string firstTokens(const vector<signed char>& t,int L,int m){ string out; int z=0; for(int i=L;i<(int)t.size();i++){ if(t[i]<0) return ""; out.push_back('0'+t[i]); if(t[i]==0){ if(++z==m) return out; } } return ""; }
int main(int argc,char**argv){ m=atoi(argv[1]); string cf=argv[2]; long LIM=atol(argv[3]);
 { ifstream f(cf); int q; string w; while(f>>q>>w) C.push_back({q,w}); M=C[0].second.size(); }
 // real start
 string r0; { vector<signed char> t(4000,0); int p=2000,q=0,lo=p; for(int n=0;n<200000;n++){ int a=t[p]; t[p]=W[q][a]; p+=Mv[q][a]; q=Q[q][a]; lo=min(lo,p);
   if(n>100){ int L=lo; while(t[L]==0&&L<p) L++; string ft; int z=0,i=L; while(z<m){ ft.push_back('0'+t[i]); if(t[i]==0) z++; i++; } if(p>i+M+5){ r0=ft; break; } } } }
 printf("start %s\n",r0.c_str());
 unordered_map<string,int> S; vector<string> order; S[r0]=0; order.push_back(r0);
 map<string,long> bad; size_t qi=0; int maxlen=0; set<string> pref;
 const int OFF=3000;
 while(qi<order.size() && (long)order.size()<LIM){
  string reg=order[qi++];
  for(auto& cw: C){
   int len=reg.size(); vector<signed char> t(OFF+len+M+2, -1);
   for(int i=0;i<OFF;i++) t[i]=0;
   for(int i=0;i<len;i++) t[OFF+i]=reg[i]-'0';
   for(int i=0;i<M;i++) t[OFF+len+i]=cw.second[i]-'0';
   int p=OFF+len, q=cw.first; string res; bool ok=false;
   for(long n=0;n<MAXSTEPS;n++){
     if(p<1){ bad["LEFTFAR"]++; break; }
     int a=t[p];
     if(a<0){ int L=0; while(t[L]==0) L++; res=firstTokens(t,L,m); if(res.empty()){bad["UNK"]++;} else ok=true; break; }
     if(q==3&&a==0){ bad["HALT"]++; if(bad["HALT"]<4) printf("HALT region %s carry %c %s\n",reg.c_str(),'A'+cw.first,cw.second.c_str()); break; }
     t[p]=W[q][a]; p+=Mv[q][a]; q=Q[q][a];
     if(n==MAXSTEPS-1) bad["LONG"]++;
   }
   if(ok && !S.count(res)){ S[res]=order.size(); order.push_back(res); maxlen=max(maxlen,(int)res.size()); { int z=0; size_t k=0; for(;k<res.size();k++){ if(res[k]=='0' && ++z==8) break; } pref.insert(res.substr(0,k+1)); } }
  }
  if(qi%5000==0){ printf("processed %zu regions %zu maxlen %d prefixes8 %zu bad:",qi,order.size(),maxlen,pref.size()); for(auto&x:bad) printf(" %s=%ld",x.first.c_str(),x.second); printf("\n"); fflush(stdout);} }
 printf("DONE processed %zu regions %zu maxlen %d bad:",qi,order.size(),maxlen); for(auto&x:bad) printf(" %s=%ld",x.first.c_str(),x.second); printf("\n");
 if(qi==order.size()){ FILE*o=fopen(("regions_"+to_string(m)+".txt").c_str(),"w"); for(auto&s:order) fprintf(o,"%s\n",s.c_str()); fclose(o);} 
}
