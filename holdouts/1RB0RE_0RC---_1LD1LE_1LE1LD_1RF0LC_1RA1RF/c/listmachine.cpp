// The list machine of lean/End.lean (`astep`), as py/listmachine.py does it, in C++ (about 1,000 times faster).
//
// Lists are nearest-first vectors of letters (false = a, true = b or c).  A state is T (k = 0), T2 (k = 1: near part w,
// far part O) or EO (k = 2; zk = 1 if there is a far part).  As in the Python version a step that the right end hands
// back (a 'V' state there) counts as a step of its own, so step numbers run a little ahead of py/listmachine.py's.
// Prints every time E reads the last 1 (EO), every crossing turn with blank end whose frozen word has no witness
// (lean/Race.lean), and a progress line every 100,000 steps; stops with DANGER if `astep` would return none.
//
//   g++ -O2 -o listmachine listmachine.cpp && ./listmachine 1000000
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
static string B(const V&v){string s;for(char c:v)s+=char(48+c);return s;}
int main(int argc,char**argv){
  long long K=atoll(argv[1]);
  St st{2,V{1,0},V(),V(),1,0,0}; long long k=-1, nw=0, tot=0, eo=0, kinds[3]={0,0,0}; size_t zmax=0;
  for(long long i=0;i<K;i++){
    if(st.k==2){ eo++; k=0;
      printf("step %lld: E reads the last 1, %s, zone %zu letters%s%s\n",i,st.zk?"during a crossing":"no crossing",st.w.size(),
             st.zk&&st.w.size()<=60?", near part ":"", st.zk&&st.w.size()<=60?B(st.w).c_str():""); }
    if(!step1(st)){printf("DANGER at %lld: %s\n",i,dmsg.c_str());return 1;}
    kinds[st.k]++; zmax=max(zmax,st.w.size()+st.O.size());
    if(st.k==1&&!st.r){ if(k>=0)k++; tot++; if(!witness(st.s)){ nw++; printf("  no witness: step %lld, bounce %lld after it, s = %s\n",i,k,st.s.empty()?"empty":B(st.s).c_str());}}
    if((i+1)%100000==0||i+1==K){printf("%lld steps: T %lld, T2 %lld, EO %lld; largest zone %zu letters; crossing turns with blank end %lld, without a witness %lld\n",
       i+1,kinds[0],kinds[1],kinds[2],zmax,tot,nw); fflush(stdout);}
  }
}
