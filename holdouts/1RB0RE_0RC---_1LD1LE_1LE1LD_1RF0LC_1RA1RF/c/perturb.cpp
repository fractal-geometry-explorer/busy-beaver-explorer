// Perturbed orbits of the list machine (lean/End.lean): how often does a machine-like orbit fail, and does it halt?
//
// Run the list machine from blank tape for I list steps to a turn T (the end of a crossing), keep the last K letters
// of the frozen word and replace the rest by random letters (and the prefix bit), then run on for E more crossing
// starts.  The next crossing start depends only on the far end of the frozen word, so for small K the orbit agrees with
// the real one at first and then drifts into orbits the machine could have taken.  At each failure of `astep` the
// configuration (`cfg` of End.lean) is rebuilt on a tape and the real machine is run from it for up to H steps.
//
//   g++ -O2 -o perturb perturb.cpp && ./perturb 186 10 1000 9 11 1000000000
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

static const char *M = "1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF";
static void lt(vector<char>&o,int x){ if(x){o.push_back(0);o.push_back(1);} else {o.push_back(1);o.push_back(1);} }
// the configuration cfg (End.lean) of a list state: cells left of the head nearest first, cells from the head on; state E
static void cfgOf(const St&x,V&L,V&R){ L.clear(); R.clear();
  if(x.k==1){ for(char c:x.w) lt(L,c); L.push_back(1); for(char c:x.O) lt(L,c); if(x.p) L.push_back(1); lt(R,0); for(char c:x.s) lt(R,c); if(x.r) R.push_back(1); }
  else if(x.k==0){ for(char c:x.w) lt(L,c); if(x.p) L.push_back(1); lt(R,0); for(char c:x.s) lt(R,c); if(x.r) R.push_back(1); }
  else { for(char c:x.w) lt(L,c); if(x.zk){ L.push_back(1); for(char c:x.O) lt(L,c);} if(x.p) L.push_back(1); R.push_back(1); } }
// run the machine from that configuration: number of steps to a halt, or -1
static long long runTM(const St&x,long long H){ V L,R; cfgOf(x,L,R); long SZ=(long)(L.size()+R.size())*4+(1L<<22);
  vector<unsigned char> t(SZ,0); long h=SZ/2; for(size_t i=0;i<L.size();i++) t[h-1-i]=L[i]; for(size_t i=0;i<R.size();i++) t[h+i]=R[i];
  int s=4; for(long long i=0;i<H;i++){ int c=t[h]; const char*q=M+s*7+c*3; if(q[0]=='-') return i; t[h]=q[0]-'0'; h+=q[1]=='R'?1:-1; s=q[2]-'A'; if(h<1||h>=SZ-1) return -2; } return -1; }
static bool isStart(const St&x){ if(!(x.k==1&&x.r==1&&x.s.empty())) return false; for(char c:x.w) if(c) return false; return true; }
int main(int argc,char**argv){
  long long I=atoll(argv[1]); int K=atoi(argv[2]); int trials=atoi(argv[3]); int E=atoi(argv[4]); srand(atoi(argv[5])); long long H=atoll(argv[6]);
  St st{2,V{1,0},V(),V(),1,0,0}; for(long long i=0;i<I;i++) step1(st);
  if(st.k!=0){printf("list step %lld is not a turn T\n",I);return 1;}
  vector<long long> fail(E+1,0), halt(E+1,0), reach(E+1,0);
  for(int t=0;t<trials;t++){
    St x=st; size_t n=x.s.size(); for(size_t q=0;q+K<n;q++) x.s[q]=rand()&1; x.p=rand()&1;
    int ep=0; reach[0]++;
    while(ep<E){ St prev=x; if(!step1(x)){ fail[ep]++; long long r=runTM(prev,H); if(r>=0) halt[ep]++;
        printf("trial %d, crossing %d after the cut: astep fails; the machine %s\n",t,ep,r>=0?"halts":"does not halt in H steps"); fflush(stdout); break; }
      if(isStart(x)){ ep++; reach[ep]++; } }
  }
  for(int e=0;e<=E;e++) printf("crossing %d after the cut: %lld orbits reach it, %lld fail in it, %lld of those halt\n",e,reach[e],fail[e],halt[e]);
}
