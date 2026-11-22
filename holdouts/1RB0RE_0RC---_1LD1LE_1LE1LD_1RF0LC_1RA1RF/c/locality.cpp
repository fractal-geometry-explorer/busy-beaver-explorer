// Locality of the growing phase: the next crossing start depends only on the far end of the frozen word.
//
// Run the list machine from blank tape for I list steps to a turn T (the end of a crossing).  Then, T times, keep the
// last K letters of the frozen word, replace the rest by random letters, and (MODE bits) also cut the frozen word to a
// random length (1), replace the zone by random letters (2), flip the prefix at random (4); run to the next crossing
// start and print its near part a^m and the first 30 letters of its far part (as a 4-cell word).
//
//   g++ -O2 -o locality locality.cpp && ./locality 12240 200 12 7     (all 13 lines agree)
//   ./locality 12240 30 20 0                                          (they do not)
#include <bits/stdc++.h>
using namespace std;
typedef vector<char> V;
struct St{int k; V w,O,s; int p,r; int zk; }; // k:0=T(w,p,s,r) 1=T2(N=w,O,p,s,r) 2=EO(W=w, zk: 0 pre p, 1 o O p)
static void sx(int q,const V&ws,V&out){out.resize(ws.size());for(size_t i=0;i<ws.size();i++){q^=ws[i];out[i]=q;}}
static int par(int q,const V&ws){for(char a:ws)q^=a;return q;}
// rswL(e, W, xs): returns W (nearest first), e, rest (has) 
static void rswL(int e,const V&W0,const V&xs,V&W,int&eo,bool&has,V&rest){
  V acc; size_t i=0; has=false;
  for(;i<xs.size();i++){int x=xs[i]; if(e&&!x){has=true;break;} e^=x; acc.push_back(e);}
  W.clear(); W.reserve(acc.size()+W0.size()); for(size_t j=acc.size();j-->0;)W.push_back(acc[j]); W.insert(W.end(),W0.begin(),W0.end());
  eo=e; rest.clear(); if(has) rest.assign(xs.begin()+i+1,xs.end());
}
static void canon(St&st){
  if(st.k==1){ size_t z=0; while(z<st.O.size()&&!st.O[z])z++; for(size_t j=0;j<z;j++)st.w.push_back(0); st.O.erase(st.O.begin(),st.O.begin()+z);
    if(st.O.empty()){ if(!st.p){st.k=0;st.p=1;} else {st.w.push_back(0);st.k=0;st.p=0;} } }
  else if(st.k==2&&st.zk==1){ size_t z=0; while(z<st.O.size()&&!st.O[z])z++; for(size_t j=0;j<z;j++)st.w.push_back(0); st.O.erase(st.O.begin(),st.O.begin()+z);
    if(st.O.empty()){ st.zk=0; if(!st.p){st.p=1;} else {st.w.push_back(0);st.p=0;} } }
}
long long danger=0; string dmsg;
// end(W,e,r,Z): returns new state; virtual flag irrelevant
static bool endf(const V&W,int e,int r,int zk,const V&O,int p,St&out){
  if(!e&&!r){ if(zk==0){out={1,V(),W,V(),p,1,0}; return true;} dmsg="A: F reaches blank end inside a crossing"; return false; }
  if(e&&r){ out.k=2; out.w=W; out.zk=zk; out.O=O; out.p=p; out.s.clear(); out.r=0; return true; }
  V W2; W2.push_back(0); W2.insert(W2.end(),W.begin(),W.end());
  if(zk==0){ out={0,W2,V(),V(),p,1,0}; return true;}
  out={1,W2,O,V(),p,1,0}; return true;
}
static bool bounce_plain(const V&w,int p,const V&tail,int r,St&out){
  V t; sx(1,w,t); V xs(t.rbegin(),t.rend()); xs.insert(xs.end(),tail.begin(),tail.end());
  V W,rest; int e; bool has; V W0{0}; rswL(0,W0,xs,W,e,has,rest);
  int p2=p^par(1,w);
  if(has){ out={0,W,V(),rest,p2,r,0}; return true;}
  return endf(W,e,r,0,V(),p2,out);
}
static bool bounce_o(const V&N,const V&O,int p,const V&tail,int r,St&out){
  int q=par(1,N); V O2;
  if(q){ assert(O[0]); O2=O; O2[0]=0; }
  else { V t; sx(0,O,t); V xs(t.rbegin(),t.rend()); V W1,r1; int e1; bool has; V W0{0}; rswL(0,W0,xs,W1,e1,has,r1);
    if(has||e1){ dmsg="even bounce blocked by far part"; return false;}
    p=p^par(0,O); O2=W1; }
  V t; sx(1,N,t); V xs(t.rbegin(),t.rend()); xs.insert(xs.end(),tail.begin(),tail.end());
  V W2,rest; int e2; bool has; rswL(0,V(),xs,W2,e2,has,rest);
  if(has){ out={1,W2,O2,rest,p,r,0}; return true;}
  return endf(W2,e2,r,1,O2,p,out);
}
static bool step1(St&st){ // one list step incl. virtual continuation as in python step()
  canon(st); St out; bool ok;
  if(st.k==0){ V tail{1}; tail.insert(tail.end(),st.s.begin(),st.s.end()); ok=bounce_plain(st.w,st.p,tail,st.r,out);}
  else if(st.k==1){ V tail{1}; tail.insert(tail.end(),st.s.begin(),st.s.end()); ok=bounce_o(st.w,st.O,st.p,tail,st.r,out);}
  else { if(st.zk==0) ok=bounce_plain(st.w,st.p,V(),0,out); else ok=bounce_o(st.w,st.O,st.p,V(),0,out);}
  if(!ok) return false; st=out; canon(st); return true;
}

static bool witness(const V&s){ // 0 then odd run of 1s then 0 or end
  size_t n=s.size(); for(size_t i=0;i<n;i++) if(!s[i]){ size_t j=i+1; while(j<n&&s[j])j++; if(((j-i-1)&1)) return true; i=j-1; }
  return false; }

static string B(const V&v,size_t n){string s;for(size_t i=0;i<v.size()&&i<n;i++)s+=char(48+v[i]);return s;}
int main(int argc,char**argv){
  long long I=atoll(argv[1]); size_t K=atoi(argv[2]); int trials=atoi(argv[3]); int mode=atoi(argv[4]); srand(3);
  St st{2,V{1,0},V(),V(),1,0,0}; for(long long i=0;i<I;i++) step1(st);
  if(st.k!=0){printf("list step %lld is not a turn T\n",I);return 1;}
  for(int t=0;t<=trials;t++){
    St x=st;
    if(t>0){ size_t n=x.s.size(); for(size_t q=0;q+K<n;q++) x.s[q]=rand()&1;
      if((mode&1)&&n>K){ size_t cut=rand()%(n-K); x.s.erase(x.s.begin(),x.s.begin()+cut); }
      if(mode&2) for(auto&c:x.w) c=rand()&1;
      if(mode&4) x.p=rand()&1; }
    bool ok=true;
    while(true){ if(!step1(x)){ok=false;break;} bool z=x.k==1&&x.r==1&&x.s.empty(); for(char c:x.w) if(c) z=false; if(z) break; }
    if(!ok){ printf("%s: astep fails\n",t?"perturbed":"real"); continue; }
    V ws; for(size_t q=2;q<x.O.size();q+=2) ws.push_back(x.O[q]);
    printf("%s: next crossing start a^%zu, far part u %s...\n",t?"perturbed":"real     ",x.w.size(),B(ws,30).c_str());
  }
}
