// A bit-parallel list machine for 1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF (lean/End.lean `astep`), 64 letters per
// machine word, for the halt hunt on the real orbit.  Same steps and output as listmachine.cpp; `verify` checks it
// against the byte version state for state.
//
// Lists are stored farthest-first (index 0 = the far end), so the near end is the back.  Then one bounce needs no
// reversal: reading `sx q w` backwards is the exclusive running XOR of the stored word, and the swept zone comes out in
// stored order.  The frozen word s is a stack whose top is its nearest letter.  A bounce is one fused pass (both running
// XORs and the rswL stop test), split over NT threads by a parity pre-pass once the zone has more than TH words.
//
//   g++ -O3 -march=native -fopenmp -o bitlist bitlist.cpp
//   ./bitlist verify 150000                          compare with the byte version for 150,000 steps
//   NT=3 ./bitlist run 100000000 ck.bin [resume.bin] run; checkpoint to ck.bin every 10 minutes; on a failure of
//                                                    astep the state before it goes to ck.bin.fail
//   ./bitlist tm 1000000000 ck.bin.fail              rebuild the tape of a saved state, run the machine up to H steps
#include <bits/stdc++.h>
using namespace std;
// The byte version (as in listmachine.cpp and perturb.cpp), for `verify` and for rebuilding the tape (`tm`).
namespace byt {
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

}
typedef uint64_t u64;

static inline u64 rbit(u64 x){ x=__builtin_bswap64(x);
  x=((x>>4)&0x0F0F0F0F0F0F0F0FULL)|((x&0x0F0F0F0F0F0F0F0FULL)<<4);
  x=((x>>2)&0x3333333333333333ULL)|((x&0x3333333333333333ULL)<<2);
  x=((x>>1)&0x5555555555555555ULL)|((x&0x5555555555555555ULL)<<1); return x; }
static inline u64 msk(int m){ return m>=64?~0ULL:((1ULL<<m)-1); }
static inline u64 pfx(u64 y){ y^=y<<1; y^=y<<2; y^=y<<4; y^=y<<8; y^=y<<16; y^=y<<32; return y; }

struct BV {
  vector<u64> a; size_t base=0, n=0;
  BV(){ a.assign(64,0); base=16*64; }
  void ensure(size_t bits){ if(base+bits+128>a.size()*64) a.resize(max(a.size()*2,(base+bits+128)/64+1),0); }
  int get(size_t i)const{ size_t g=base+i; return (a[g>>6]>>(g&63))&1; }
  void set(size_t i,int b){ size_t g=base+i; if(b) a[g>>6]|=1ULL<<(g&63); else a[g>>6]&=~(1ULL<<(g&63)); }
  u64 get64(size_t i)const{ size_t g=base+i, w=g>>6; int o=g&63; u64 lo=a[w]>>o; if(o) lo|=a[w+1]<<(64-o); return lo; }
  void clear(){ if(a.size()<64) a.resize(64,0); base=16*64; n=0; }
  void append64(u64 x,int m){ if(m<=0) return; ensure(n+64); x&=msk(m); size_t g=base+n, w=g>>6; int o=g&63;
    a[w]=(a[w]&msk(o))|(x<<o); if(o&&o+m>64) a[w+1]=(a[w+1]&~msk(o+m-64))|(x>>(64-o)); n+=m; }
  void push_back(int b){ append64(b,1); }
  int back()const{ return get(n-1); }
  void pop_back(size_t k){ n-=k; }
  void push_front(int b){ if(base==0){ size_t used=(n+63)/64+2, hw=used/2+16; if(a.size()<used+2*hw) a.resize(used+2*hw,0);
      memmove(&a[hw],&a[0],used*8); memset(&a[0],0,hw*8); base=hw*64; } base--; n++; set(0,b); }
  int parity()const{ int q=0; size_t i=0; for(;i+64<=n;i+=64) q^=__builtin_parityll(get64(i)); if(i<n) q^=__builtin_parityll(get64(i)&msk(n-i)); return q; }
  void appendRange(const BV&s,size_t from,size_t to){ for(size_t i=from;i<to;i+=64){ int m=min<size_t>(64,to-i); append64(s.get64(i),m);} }
  // append s[to-1], s[to-2], ..., s[from]
  void appendRev(const BV&s,size_t from,size_t to){ size_t e=to; while(e>from){ int m=min<size_t>(64,e-from); u64 x=s.get64(e-m)&msk(m); append64(rbit(x)>>(64-m),m); e-=m; } }
};

struct BS { int k; BV w,O,s; int p,r,zk; };
string dmsg;

// rswL scan: feeds chunks; out gets the running XOR values; stops where e = 1 meets x = 0.
struct Scan { BV*out; int e; bool stopped=false; size_t pos=0;
  bool feed(u64 x,int m){ x&=msk(m); u64 y=pfx(x); if(e) y=~y; y&=msk(m); u64 hit=y&~x&msk(m);
    if(hit){ int idx=__builtin_ctzll(hit); out->append64(y,idx); pos+=idx; stopped=true; return true; }
    out->append64(y,m); pos+=m; e=(y>>(m-1))&1; return false; } };

static BV AT, NW, NO; // scratch
static int NT=1; static size_t TH=4096;
// One bounce of the swept part w, fused: A = exclusive running XOR of w from c = cfix ^ parity(w), then the rswL scan of
// A from e = 0 (and of the tail 1 :: s when hasTail).  out must end on a word boundary.  Returns the class (0 no stop,
// 1 stop inside A at where, 2 stop in the tail after popping where letters of s), and sets pw, e.  On class 1, AT holds
// A[where+1 ..) in order.
static vector<int> Bpx, Bpa; static vector<size_t> Bw0, Bw1; static vector<int> Bcc, Bee; static vector<long> Bhit; static vector<u64> Bhcc;
static int scanW(const BV&w,int cfix,BV&out,bool hasTail,const BV&s,size_t&where,int&pw,int&eOut){
  size_t n=w.n, nwd=(n+63)/64; assert((out.base+out.n)%64==0); out.ensure(out.n+n+128); size_t ob=(out.base+out.n)/64;
  int T = nwd>TH ? NT : 1; Bpx.assign(T,0); Bpa.assign(T,0); Bw0.resize(T); Bw1.resize(T); Bcc.resize(T+1); Bee.resize(T+1); Bhit.assign(T,-1); Bhcc.assign(T,0);
  for(int b=0;b<T;b++){ Bw0[b]=nwd*b/T; Bw1[b]=nwd*(b+1)/T; }
  #pragma omp parallel for num_threads(T) schedule(static,1) if(T>1)
  for(int b=0;b<T;b++){ size_t L=min(n,Bw1[b]*64)-Bw0[b]*64; u64 am=(L&1)?0xAAAAAAAAAAAAAAAAULL:0x5555555555555555ULL; int px=0,pa=0;
    for(size_t i=Bw0[b];i<Bw1[b];i++){ int m=min<size_t>(64,n-i*64); u64 x=w.get64(i*64)&msk(m); px^=__builtin_parityll(x); pa^=__builtin_parityll(x&am); }
    Bpx[b]=px; Bpa[b]=pa; }
  pw=0; for(int b=0;b<T;b++) pw^=Bpx[b];
  int c=cfix^pw; Bcc[0]=c; Bee[0]=0;
  for(int b=0;b<T;b++){ size_t L=min(n,Bw1[b]*64)-Bw0[b]*64; Bcc[b+1]=Bcc[b]^Bpx[b]; Bee[b+1]=Bee[b]^Bpa[b]^(Bcc[b]&(int)(L&1)); }
  #pragma omp parallel for num_threads(T) schedule(static,1) if(T>1)
  for(int b=0;b<T;b++){ u64 ccm=Bcc[b]?~0ULL:0, eem=Bee[b]?~0ULL:0;
    for(size_t i=Bw0[b];i<Bw1[b];i++){ int m=min<size_t>(64,n-i*64); u64 mm=msk(m); u64 x=w.get64(i*64)&mm; u64 Q=pfx(x)^ccm; u64 a=(Q^x)&mm; u64 y=(pfx(a)^eem)&mm;
      out.a[ob+i]=y; u64 hit=y&~a&mm; if(hit){ Bhit[b]=(long)(i*64+__builtin_ctzll(hit)); Bhcc[b]=ccm; break; }
      ccm=((Q>>(m-1))&1)?~0ULL:0; eem=((y>>(m-1))&1)?~0ULL:0; } }
  for(int b=0;b<T;b++) if(Bhit[b]>=0){ size_t iA=Bhit[b]; out.n+=iA; where=iA;
      // A from the stop word on
      AT.clear(); size_t i0=iA/64; u64 ccm=Bhcc[b];
      for(size_t i=i0;i*64<n;i++){ int m=min<size_t>(64,n-i*64); u64 mm=msk(m); u64 x=w.get64(i*64)&mm; u64 Q=pfx(x)^ccm; u64 a=(Q^x)&mm;
        size_t lo=i*64; if(lo+m>iA+1){ size_t from=iA+1>lo?iA+1-lo:0; AT.append64(a>>from,m-from); } ccm=((Q>>(m-1))&1)?~0ULL:0; }
      return 1; }
  out.n+=n; int e=Bee[T];
  if(!hasTail){ eOut=e; return 0; }
  Scan sc{&out,e}; sc.feed(1,1);
  size_t rem=s.n, used=0;
  while(rem>0){ int m=min<size_t>(64,rem); u64 x=s.get64(rem-m)&msk(m); x=rbit(x)>>(64-m); size_t before=sc.pos;
    if(sc.feed(x,m)){ where=used+(sc.pos-before)+1; return 2; } used+=m; rem-=m; }
  eOut=sc.e; return 0;
}
static void applyRest(BS&st,int cls,size_t where,bool hasTail){
  if(cls==1){ if(hasTail) st.s.push_back(1); else st.s.clear(); st.s.appendRev(AT,0,AT.n); }
  else if(cls==2){ st.s.pop_back(where); }
}
static bool endf(BS&st,BV&W,int e,int r,int zk,int p){
  if(!e&&!r){ if(zk==0){ st.k=1; swap(st.O,W); st.w.clear(); st.s.clear(); st.p=p; st.r=1; st.zk=0; return true;} dmsg="A: F reaches blank end inside a crossing"; return false; }
  if(e&&r){ st.k=2; swap(st.w,W); st.zk=zk; if(!zk) st.O.clear(); st.p=p; st.s.clear(); st.r=0; return true; }
  W.push_back(0); swap(st.w,W); st.s.clear(); st.p=p; st.r=1; st.zk=0;
  if(zk==0){ st.k=0; st.O.clear(); } else st.k=1; return true;
}
static void startOut(BV&o,bool zero){ o.clear(); if(zero){ o.base=16*64-1; o.n=1; o.a[15]&=~(1ULL<<63); } }
static bool bounce_plain(BS&st,bool hasTail,int r){
  startOut(NW,true); size_t where=0; int pw,e=0; int cls=scanW(st.w,1,NW,hasTail,st.s,where,pw,e); int p2=st.p^(1^pw);
  if(cls){ applyRest(st,cls,where,hasTail); swap(st.w,NW); st.k=0; st.O.clear(); st.p=p2; st.r=r; st.zk=0; return true; }
  if(hasTail) st.s.clear();
  return endf(st,NW,e,r,0,p2);
}
static bool bounce_o(BS&st,bool hasTail,int r){
  int q=1^st.w.parity(); int p=st.p; bool flip=false;
  if(q){ assert(st.O.back()); flip=true; }
  else { startOut(NO,true); size_t wh; int po,e1=0; int c1=scanW(st.O,0,NO,false,st.s,wh,po,e1);
    if(c1||e1){ dmsg="even bounce blocked by far part"; return false; } p^=po; }
  startOut(NW,false); size_t where=0; int pw,e=0; int cls=scanW(st.w,1,NW,hasTail,st.s,where,pw,e);
  if(!cls && !e && !r){ dmsg="A: F reaches blank end inside a crossing"; return false; }
  if(flip) st.O.set(st.O.n-1,0); else swap(st.O,NO);
  if(cls){ applyRest(st,cls,where,hasTail); swap(st.w,NW); st.k=1; st.p=p; st.r=r; st.zk=0; return true; }
  if(hasTail) st.s.clear();
  return endf(st,NW,e,r,1,p);
}
static size_t tz_back(const BV&v){ size_t z=0; size_t i=v.n; while(i>0){ int m=min<size_t>(64,i); u64 x=v.get64(i-m)&msk(m); x<<= (64-m);
    if(x){ z+=__builtin_clzll(x); return z; } z+=m; i-=m; } return z; }
static void canon(BS&st){
  if(st.k==1||(st.k==2&&st.zk==1)){ size_t z=tz_back(st.O); for(size_t j=0;j<z;j++) st.w.push_front(0); st.O.pop_back(z);
    if(st.O.n==0){ if(st.k==1) st.k=0; else st.zk=0; if(!st.p) st.p=1; else { st.w.push_front(0); st.p=0; } } }
}
static bool step1(BS&st){
  canon(st); bool ok;
  if(st.k==0) ok=bounce_plain(st,true,st.r);
  else if(st.k==1) ok=bounce_o(st,true,st.r);
  else ok = st.zk==0 ? bounce_plain(st,false,0) : bounce_o(st,false,0);
  if(!ok) return false; canon(st); return true;
}
static byt::V toNF(const BV&v){ byt::V o(v.n); for(size_t i=0;i<v.n;i++) o[i]=v.get(v.n-1-i); return o; }
static byt::St toByte(const BS&b){ byt::St s; s.k=b.k; s.w=toNF(b.w); s.O=toNF(b.O); s.s=toNF(b.s); s.p=b.p; s.r=b.r; s.zk=b.zk;
  if(s.k==0){ s.O.clear(); s.zk=0; } if(s.k==1) s.zk=0; if(s.k==2){ s.s.clear(); s.r=0; if(!s.zk) s.O.clear(); } return s; }
static bool sameSt(const byt::St&a,const byt::St&b){ return a.k==b.k&&a.w==b.w&&a.O==b.O&&a.s==b.s&&a.p==b.p&&(a.k==2||a.r==b.r)&&(a.k!=2||a.zk==b.zk); }
static bool witnessTop(const BV&s){ // on s nearest-first: 0 then odd run of 1s then 0 or end
  long n=s.n; for(long i=n-1;i>=0;i--) if(!s.get(i)){ long j=i-1; while(j>=0&&s.get(j)) j--; if(((i-j-1)&1)) return true; i=j+1; } return false; }
static void saveBV(FILE*f,const BV&v){ fwrite(&v.n,8,1,f); for(size_t i=0;i<v.n;i+=64){ u64 x=v.get64(i)&msk(min<size_t>(64,v.n-i)); fwrite(&x,8,1,f);} }
static void loadBV(FILE*f,BV&v){ size_t n; if(fread(&n,8,1,f)!=1) exit(2); v.clear(); for(size_t i=0;i<n;i+=64){ u64 x; if(fread(&x,8,1,f)!=1) exit(2); v.append64(x,min<size_t>(64,n-i)); } }
struct Ctr { long long i=0,k=-1,nw=0,tot=0,eo=0,kinds[3]={0,0,0}; size_t zmax=0; };
static void save(const char*fn,const BS&st,const Ctr&c){ string t=string(fn)+".tmp"; FILE*f=fopen(t.c_str(),"wb"); fwrite(&c,sizeof c,1,f); int h[4]={st.k,st.p,st.r,st.zk}; fwrite(h,sizeof h,1,f);
  saveBV(f,st.w); saveBV(f,st.O); saveBV(f,st.s); fclose(f); rename(t.c_str(),fn); }
static void load(const char*fn,BS&st,Ctr&c){ FILE*f=fopen(fn,"rb"); if(!f) exit(3); if(fread(&c,sizeof c,1,f)!=1) exit(2); int h[4]; if(fread(h,sizeof h,1,f)!=1) exit(2);
  st.k=h[0];st.p=h[1];st.r=h[2];st.zk=h[3]; loadBV(f,st.w); loadBV(f,st.O); loadBV(f,st.s); fclose(f); }

int main(int argc,char**argv){
  string mode=argv[1]; long long K=atoll(argv[2]); if(getenv("NT")) NT=atoi(getenv("NT")); if(getenv("TH")) TH=atol(getenv("TH"));
  BS st; st.k=2; st.w.push_back(0); st.w.push_back(1); /* W = [true,false] nearest-first */ st.p=1; st.r=0; st.zk=0;
  if(mode=="verify"){ byt::St b{2,byt::V{1,0},byt::V(),byt::V(),1,0,0};
    if(!sameSt(toByte(st),b)){ puts("start differs"); return 1; }
    for(long long i=0;i<K;i++){ bool o1=step1(st), o2=byt::step1(b); if(o1!=o2){ printf("ok differs at %lld\n",i); return 1; } if(!o1){ printf("both fail at %lld\n",i); return 0; }
      if(!sameSt(toByte(st),b)){ { auto x=toByte(st); auto P=[](const char*n,const byt::V&v){printf("%s ",n);for(char c:v)putchar(48+c);puts("");}; printf("state differs at step %lld k %d/%d p %d/%d r %d/%d\n",i,x.k,b.k,x.p,b.p,x.r,b.r); P("w",x.w);P("w",b.w);P("O",x.O);P("O",b.O);P("s",x.s);P("s",b.s); return 1; } } }
    printf("verify ok %lld\n",K); return 0; }
  if(mode=="tm"){ // ./blm2 tm H file: rebuild the tape of a saved state and run the machine for up to H steps
    Ctr c0; load(argv[3],st,c0); byt::St b=toByte(st); long long r=byt::runTM(b,K);
    printf("list step %lld, state k=%d, |w| %zu |O| %zu |s| %zu: %s %lld\n",c0.i,st.k,st.w.n,st.O.n,st.s.n,r>=0?"the machine halts after":"no halt within",r>=0?r:K); return 0; }
  const char*ck=argc>3?argv[3]:nullptr; Ctr c; if(argc>4) load(argv[4],st,c);
  auto t0=chrono::steady_clock::now(), tl=t0;
  for(;c.i<K;c.i++){ long long i=c.i;
    if(st.k==2){ c.eo++; c.k=0; printf("step %lld: E reads the last 1, %s, zone %zu letters\n",i,st.zk?"during a crossing":"no crossing",st.w.n); fflush(stdout); }
    byt::St prev; bool small=st.w.n+st.O.n+st.s.n<(1u<<26);
    if(!step1(st)){ printf("DANGER at %lld: %s\n",i,dmsg.c_str()); fflush(stdout);
      if(ck){ save((string(ck)+".fail").c_str(),st,c); } (void)small; return 1; }
    c.kinds[st.k]++; c.zmax=max(c.zmax,st.w.n+st.O.n);
    if(st.k==1&&!st.r){ if(c.k>=0) c.k++; c.tot++; if(!witnessTop(st.s)){ c.nw++; printf("  no witness: step %lld, bounce %lld after it, |s| = %zu\n",i,c.k,st.s.n); } }
    if((i+1)%100000==0||i+1==K){ double el=chrono::duration<double>(chrono::steady_clock::now()-t0).count();
      printf("%lld steps: T %lld, T2 %lld, EO %lld; largest zone %zu letters; |s| %zu; crossing turns with blank end %lld, without a witness %lld; %.0f s\n",
       i+1,c.kinds[0],c.kinds[1],c.kinds[2],c.zmax,st.s.n,c.tot,c.nw,el); fflush(stdout); }
    if(ck&&chrono::duration<double>(chrono::steady_clock::now()-tl).count()>600){ Ctr c2=c; c2.i=i+1; save(ck,st,c2); tl=chrono::steady_clock::now(); }
  }
  if(ck){ save(ck,st,c); }
}
