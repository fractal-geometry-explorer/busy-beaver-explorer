// Region closure with arrival lemma. region = first m tokens (cells L..b-1, b-1 = m-th zero).
// arrival: carry (state, cells b..b+X-1) from arrival file. exit: head at p >= b'+X where b' = current boundary.
// unknown cells (>= b+X at arrival) are branched 0/1 when read (right part is arbitrary).
#include <bits/stdc++.h>
using namespace std;
int W[6][2]={{1,1},{1,1},{1,0},{9,1},{1,0},{0,1}};
int Mv[6][2]={{1,1},{1,-1},{-1,-1},{0,-1},{1,-1},{1,1}};
int Q[6][2]={{1,5},{2,2},{3,4},{9,4},{5,1},{0,4}};
int m, X; long MAXSTEPS=1000000;
const int OFF=4000, SZ=OFF+4000;
struct Cfg{ vector<signed char> t; int p,q; long n; };
map<string,long> bad;
int boundary(const vector<signed char>&t, int L){ int z=0; for(int i=L;i<SZ;i++){ if(t[i]<0) return -1; if(t[i]==0 && ++z==m) return i+1; } return -1; }
int main(int argc,char**argv){ m=atoi(argv[1]); string af=argv[2]; long LIM=atol(argv[3]);
 vector<pair<int,string>> A; { ifstream f(af); int q; string w; while(f>>q>>w) A.push_back({q,w}); X=A[0].second.size(); }
 string r0; { vector<signed char> t(8000,0); int p=4000,q=0; for(int n=0;n<2000000;n++){ int a=t[p]; t[p]=W[q][a]; p+=Mv[q][a]; q=Q[q][a];
   if(n>100){ int L=0; while(t[L]==0) L++; int z=0,i=L; string ft; while(z<m){ ft.push_back('0'+t[i]); if(t[i]==0) z++; i++; } if(p>=i+X){ r0=ft; break; } } } }
 printf("m=%d X=%d arrivals %zu start %s\n",m,X,A.size(),r0.c_str()); fflush(stdout);
 unordered_set<string> S; vector<string> order; S.insert(r0); order.push_back(r0); size_t qi=0; long branches=0;
 while(qi<order.size() && (long)order.size()<LIM){
  string reg=order[qi++];
  for(auto& cw: A){
   vector<Cfg> stk; { Cfg c; c.t.assign(SZ,-1); for(int i=0;i<OFF;i++) c.t[i]=0; int len=reg.size(); for(int i=0;i<len;i++) c.t[OFF+i]=reg[i]-'0'; for(int i=0;i<X;i++) c.t[OFF+len+i]=cw.second[i]-'0'; c.p=OFF+len; c.q=cw.first; c.n=0; stk.push_back(c); }
   while(!stk.empty()){
    Cfg c=move(stk.back()); stk.pop_back(); vector<signed char>&t=c.t; int p=c.p,q=c.q;
    bool fin=false; int L=0; while(t[L]==0) L++;
    for(long n=c.n;n<MAXSTEPS;n++){
     if(p<2||p>=SZ-1){ bad["RANGE"]++; fin=true; break; }
     int b=-1; if(p-L>=2*m+X) b=boundary(t,L);
     if(b>=0 && p>=b+X){ string res; for(int i=L;i<b;i++) res.push_back('0'+t[i]); if(!S.count(res)){S.insert(res); order.push_back(res);} fin=true; break; }
     int a=t[p];
     if(a<0){ branches++; Cfg c2; c2.t=t; c2.t[p]=1; c2.p=p; c2.q=q; c2.n=n; stk.push_back(move(c2)); t[p]=0; a=0; }
     if(q==3&&a==0){ bad["HALT"]++; if(bad["HALT"]<=3) printf("HALT region %s arrival %c %s\n",reg.c_str(),'A'+cw.first,cw.second.c_str()); fin=true; break; }
     t[p]=W[q][a]; if(t[p]==1 && p<L) L=p; else if(t[p]==0 && p==L){ while(t[L]==0) L++; } p+=Mv[q][a]; q=Q[q][a];
    }
    if(!fin) bad["LONG"]++;
   }
  }
  if(qi%5000==0){ printf("processed %zu regions %zu branches %ld bad:",qi,order.size(),branches); for(auto&x:bad) printf(" %s=%ld",x.first.c_str(),x.second); printf("\n"); fflush(stdout);} }
 printf("DONE processed %zu regions %zu bad:",qi,order.size()); for(auto&x:bad) printf(" %s=%ld",x.first.c_str(),x.second); printf("\n");
 if(qi==order.size()){ FILE*o=fopen(("regions2_"+to_string(m)+".txt").c_str(),"w"); for(auto&s:order) fprintf(o,"%s\n",s.c_str()); fclose(o);} 
}
