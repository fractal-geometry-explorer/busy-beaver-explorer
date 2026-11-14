#include <unordered_set>
// General visit-accelerated simulator with exact big counts.  See gvis.py for the algorithm (same, in Python).
// A visit of signature (SIN, D, CTX, SOUT): the head is at q in state SIN and the D-1 cells left of it hold CTX
// (nearest first); it ends the first time the head is at q-D, in state SOUT with CTX restored.
// usage: gvis MACHINE discover [NSTEPS]
//        gvis MACHINE run SIG [MAXTOP] [MAXSEC]        SIG = e.g. C20A  (state, D, ctx bits, exit state)
//        gvis MACHINE validate SIG R NSTEPS
// A leading "m:" on MACHINE mirrors the table (left and right exchanged).
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <ctime>
#include <vector>
#include <string>
#include <unordered_map>
#include <algorithm>
using namespace std;
typedef vector<uint32_t> Big;   // little endian, no leading zeros; empty = 0
static bool isz(const Big&a){ return a.empty(); }
static void trim(Big&a){ while(!a.empty()&&a.back()==0) a.pop_back(); }
static Big bsmall(uint64_t v){ Big a; while(v){ a.push_back((uint32_t)v); v>>=32;} return a; }
static uint32_t divmod(Big&a,uint32_t d){ uint64_t r=0; for(int i=(int)a.size()-1;i>=0;i--){ uint64_t c=(r<<32)|a[i]; a[i]=(uint32_t)(c/d); r=c%d; } trim(a); return (uint32_t)r; }
static void muladd(Big&a,uint32_t m,uint32_t add){ uint64_t c=add; for(size_t i=0;i<a.size();i++){ c+= (uint64_t)a[i]*m; a[i]=(uint32_t)c; c>>=32; } while(c){ a.push_back((uint32_t)c); c>>=32; } trim(a); }
static void dec(Big&a){ for(size_t i=0;i<a.size();i++){ if(a[i]--) break; } trim(a); }
static long bits(const Big&a){ if(a.empty()) return 0; long b=(a.size()-1)*32; uint32_t t=a.back(); while(t){ b++; t>>=1; } return b; }
static bool gt(const Big&a,uint32_t v){ return a.size()>1 || (a.size()==1 && a[0]>v); }


// ---- sparse counts: value = sum coef * 2^(e+sh), terms sorted by e descending (lowest at the back) ----
struct Stop{};
static void die(const char*why);
typedef __int128 i128;
struct Cnt {
  vector<pair<long,long>> t; long sh=0;
  void addlow(long a){ if(!a) return; if(!t.empty() && t.back().first+sh==0){ t.back().second+=a; long c=t.back().second; if(c==0) t.pop_back(); else if(c>(1L<<61)||c<-(1L<<61)) die("ANOM coef overflow"); } else t.push_back({-sh,a}); }
  // true if the value is < 2^62; then v is the value and the representation is collapsed
  bool small(long&v){
    if(t.empty()){ v=0; return true; }
    i128 acc=0; long pe=t[0].first; const i128 LIM=((i128)1)<<100;
    for(size_t i=0;i<t.size();i++){ long g=pe-t[i].first;
      if(acc!=0 && (g>=66 || acc>=(LIM>>g) || -acc>=(LIM>>g))){ if(acc<0) die("ANOM negative count"); return false; }
      acc=(acc<<g)+t[i].second; pe=t[i].first; }
    long e=pe+sh; if(e<0) die("ANOM fractional count");
    if(acc<0) die("ANOM negative count");
    if(acc!=0 && (e>=62 || acc>=(((i128)1)<<(62-e)))) return false;
    v=(long)(acc<<e); if(v<(1L<<40)){ t.clear(); sh=0; if(v) t.push_back({0,v}); } return true; }
  bool isz(){ if(t.empty()) return true; if(t.size()==1) return false; long v; return small(v)&&v==0; }
  bool gt(long x){ long v; return !small(v)||v>x; }
  int half(){ sh-=1; if(t.empty()||t.back().first+sh!=-1) return 0; long c=t.back().second; t.pop_back(); int r=(int)(c&1); addlow(c>>1); return r; }
  long bits(){ return t.empty()?0:t[0].first+sh+1; }
};
static Cnt csmall(long v){ Cnt c; if(v) c.t.push_back({0,v}); return c; }
// dense fallback (rare): exact conversion both ways
static void bsubshift(Big&a,unsigned long v,long e,bool neg){ // a += or -= v<<e
  size_t w=e/32; int b=e%32; unsigned __int128 x=((unsigned __int128)v)<<b; if(a.size()<w+6) a.resize(w+6,0);
  if(!neg){ uint64_t c=0; for(size_t i=w;i<a.size();i++){ uint64_t s=(uint64_t)a[i]+(uint32_t)x+c; a[i]=(uint32_t)s; c=s>>32; x>>=32; if(!x&&!c) break; } }
  else { int64_t br=0; for(size_t i=w;i<a.size();i++){ int64_t s=(int64_t)a[i]-(int64_t)(uint32_t)x-br; br=0; if(s<0){ s+=((int64_t)1<<32); br=1; } a[i]=(uint32_t)s; x>>=32; if(!x&&!br) break; } }
}
static Big todense(Cnt&c){ Big a; long top=c.t.empty()?0:c.t[0].first+c.sh; a.assign(top/32+8,0);
  for(auto&p:c.t) if(p.second>0) bsubshift(a,p.second,p.first+c.sh,false);
  for(auto&p:c.t) if(p.second<0) bsubshift(a,-p.second,p.first+c.sh,true);
  trim(a); return a; }
static Cnt fromdense(const Big&a){ Cnt c; vector<pair<long,long>> v; long nb=(long)a.size()*32; int carry=0;
  for(long i=0;i<=nb;i++){ int b=(i<nb?((a[i/32]>>(i%32))&1):0)+carry; if(b==2){ carry=1; continue; } if(b==0){ carry=0; continue; }
    int nx=(i+1<nb?((a[(i+1)/32]>>((i+1)%32))&1):0); if(nx){ v.push_back({i,-1}); carry=1; } else { v.push_back({i,1}); carry=0; } }
  for(long i=(long)v.size()-1;i>=0;i--) c.t.push_back(v[i]); return c; }
static long nfallback=0;
static uint32_t cdivmod(Cnt&n,uint32_t L){ if(L==1) return 0; if(L==2) return n.half(); if(L==4){ int a=n.half(); int b=n.half(); return a+2*b; } if(L==8){ int a=n.half(); int b=n.half(); int c=n.half(); return a+2*b+4*c; }
  long v; if(n.small(v)){ uint32_t r=v%L; n=csmall(v/L); return r; }
  nfallback++; Big d=todense(n); uint32_t r=divmod(d,L); n=fromdense(d); return r; }
static void cmuladd(Cnt&n,uint32_t M,uint32_t add){
  if(M==0){ n=csmall(add); return; }
  if((M&(M-1))==0){ int j=__builtin_ctz(M); n.sh+=j; n.addlow(add); return; }
  for(auto&p:n.t){ if(p.second>(1L<<40)||p.second<-(1L<<40)){ nfallback++; Big d=todense(n); muladd(d,M,add); n=fromdense(d); return; } }
  for(auto&p:n.t) p.second*=M; n.addlow(add); }
static int tmw[6][2], tmd[6][2], tms[6][2];
#define TSZ (1L<<30)
static uint8_t *tape; static long lo=0, hi=0;
static uint64_t thash=0;
static inline uint64_t zob(long p){ uint64_t x=(uint64_t)p*0x9E3779B97F4A7C15ULL; x^=x>>29; x*=0xBF58476D1CE4E5B9ULL; x^=x>>32; return x; }
static inline void wr(long p,int v){ if(tape[p]!=v){ tape[p]=v; thash^=zob(p);} if(p>=hi) hi=p+1; if(p<lo) lo=p; }

static void cadd(Cnt&a, Cnt&b){ vector<pair<long,long>> r; size_t i=0,j=0;
  while(i<a.t.size()||j<b.t.size()){
    long ea= i<a.t.size()? a.t[i].first+a.sh : -1, eb= j<b.t.size()? b.t[j].first+b.sh : -1;
    if(ea>eb){ r.push_back({ea,a.t[i].second}); i++; } else if(eb>ea){ r.push_back({eb,b.t[j].second}); j++; }
    else { long c=a.t[i].second+b.t[j].second; if(c) r.push_back({ea,c}); i++; j++; } }
  a.t.swap(r); a.sh=0; }
struct Seg{ int f; Cnt n; };
typedef vector<Seg> Word;
static bool isform[6]; static int exitst[6], fD[6]={1,1,1,1,1,1}, fctx[6];
static inline bool ctxok(int st,long pos){ for(int i=0;i<fD[st]-1;i++) if(tape[pos-1-i]!=((fctx[st]>>i)&1)) return false; return true; }
static long topvis=0, nsingle=0, nraw=0, rawsteps=0, nbatch=0, ncyc=0, maxbits=0, maxtop=0, maxsec=0, maxraw=200000000, nflush=0, maxseg=0;
static int depth=0, maxdepth=0; static size_t maxterms=0; static long maxq=0, nmerge=0;
static time_t t0;
#define MAXW 14
struct Rule { uint16_t out; uint8_t nk; uint8_t f[7]; };
static unordered_map<uint32_t,Rule> rules; static bool haveW[6][MAXW+1];
struct Cyc { int stamp; bool ok; int W, L, fo, M; uint8_t k[8]; uint16_t fin[8]; };
static unordered_map<uint32_t,Cyc> cycs;
static vector<pair<long,uint64_t>> recs; static long recmax=0;
static void report(const char*why){
  printf("%s topvis %ld lo %ld hi %ld singles %ld raws %ld rawsteps %ld batches %ld compressed %ld flushes %ld rules %zu maxbits %ld maxdepth %d maxterms %zu maxq %ld merges %ld fallback %ld hash %016lx t %lds\n",
    why,topvis,lo,hi,nsingle,nraw,rawsteps,nbatch,ncyc,nflush,rules.size(),maxbits,maxdepth,maxterms,maxq,nmerge,nfallback,thash,(long)(time(0)-t0)); fflush(stdout);
}
static void die(const char*why){ report(why); throw Stop(); }
static inline int win(long p,int w){ int b=0; for(int i=0;i<w;i++) b|=tape[p+i]<<i; return b; }
static inline void setwin(long p,int w,int b){ for(int i=0;i<w;i++) wr(p+i,(b>>i)&1); }
static void process(long p, Word in);
static bool halted=false; static long ckevery=0; static const char*ckname=0;
static void checkpoint(long pos,int st);
static void raw(long p,int f,bool top){
  long pos=p, tmax= top? p-1 : p, n=0; int st= top?0:f; int sv[4]={0,0,0,0};
  nraw++;
  if(!top) for(int i=0;i<fD[f]-1;i++){ sv[i]=tape[p-1-i]; tape[p-1-i]=(fctx[f]>>i)&1; }
  for(;;){
    if(isform[st] && (top||(pos>tmax && pos-fD[st]>p-fD[f])) && ctxok(st,pos)){
      if(top){ topvis++; if(recmax && (long)recs.size()<recmax) recs.push_back({pos,thash});
        if(ckevery && topvis%ckevery==0) checkpoint(pos,st);
        if((maxtop && topvis>maxtop) || (recmax && (long)recs.size()>=recmax)) die("DONE");
        if(maxsec && (topvis&63)==0 && time(0)-t0>maxsec) die("TIME"); }
      Word w1; w1.push_back({st,csmall(1)}); { int fs=st; process(pos,std::move(w1)); pos-=fD[fs]; st=exitst[fs]; }
    } else {
      int c=tape[pos];
      if(pos>tmax) tmax=pos;
      if(tmw[st][c]<0){ halted=true; printf("HALT state %c reading %d at pos %ld top visit %ld depth %d\n",'A'+st,c,pos,topvis,depth); die("HALT"); }
      if(!top && pos<p) tape[pos]=tmw[st][c]; else wr(pos,tmw[st][c]);
      pos+=tmd[st][c]; st=tms[st][c]; n++; rawsteps++;
      if(pos<=-TSZ/2+64||pos>=TSZ/2-64) die("ANOM tape overflow");
      if(!top && n>maxraw) die("ANOM raw visit too long");
      if((rawsteps&0xFFFFF)==0 && maxsec && time(0)-t0>maxsec) die("TIME");
    }
    if(!top && pos<=p-fD[f]){ if(pos!=p-fD[f]||st!=exitst[f]||!ctxok(f,p)) die("ANOM bad return"); break; }
  }
  if(!top) for(int i=0;i<fD[f]-1;i++) tape[p-1-i]=sv[i];
}
#undef X
static unordered_set<uint32_t> norule;
static bool derive(int f,int buf){
  int Df=fD[f];
  for(int w=1;w<=MAXW;w++){
    int cbuf[MAXW+4]; int*c=cbuf+4; for(int i=0;i<w;i++) c[i]=(buf>>i)&1; for(int i=0;i<Df-1;i++) c[-1-i]=(fctx[f]>>i)&1;
    int pos=0, st=f, nsub=0; uint8_t subs[7]; bool fail=false, all=false;
    for(long n=0;;n++){
      if(n>200000){ all=true; break; }
      if(pos==w){ if(!isform[st]){ fail=true; break; } int Ds=fD[st]; if(Ds-1>w+Df-1){ fail=true; break; }
        bool ok=true; for(int i=0;i<Ds-1;i++) if(c[w-1-i]!=((fctx[st]>>i)&1)) ok=false;
        if(!ok){ fail=true; break; } if(nsub>=7){ all=true; break; } if(w-Ds<= -Df){ fail=true; break; }
        subs[nsub++]=st; pos=w-Ds; st=exitst[st]; }
      else { int cc=c[pos]; if(tmw[st][cc]<0){ all=true; break; }
        c[pos]=tmw[st][cc]; pos+=tmd[st][cc]; st=tms[st][cc]; }
      if(pos<=-Df){ bool ok=(pos==-Df&&st==exitst[f]); for(int i=0;i<Df-1;i++) if(c[-1-i]!=((fctx[f]>>i)&1)) ok=false; if(!ok) all=true; break; }
    }
    if(all) break;
    if(fail) continue;
    Rule r; r.out=0; for(int i=0;i<w;i++) r.out|=c[i]<<i; r.nk=nsub; for(int i=0;i<nsub;i++) r.f[i]=subs[i];
    rules[(f<<28)|(w<<16)|(buf&((1<<w)-1))]=r; haveW[f][w]=true; return true;
  }
  norule.insert((f<<28)|buf); return false;
}
static bool match(int f,int buf,int&w,Rule&r){
  for(int pass=0;pass<2;pass++){
    for(int i=1;i<=MAXW;i++) if(haveW[f][i]){ auto it=rules.find((f<<28)|(i<<16)|(buf&((1<<i)-1))); if(it!=rules.end()){ w=i; r=it->second; return true; } }
    if(pass||norule.count((f<<28)|buf)) return false;
    if(!derive(f,buf)) return false;
  }
  return false; }
static Cyc* findcycle(int f,long p){
  int b0=win(p,MAXW); Cyc&cy=cycs[(f<<28)|b0];
  if(cy.stamp==(int)rules.size()+1) return cy.ok?&cy:nullptr;
  cy.stamp=rules.size()+1; cy.ok=false;
  int buf=b0, ws[8], ks[8], bs[8], fo=-1; bool pure=true;
  for(int L=1;L<=8;L++){
    int w; Rule r; if(!match(f,buf,w,r)) break;
    buf=(buf&~((1<<w)-1))|r.out; ws[L-1]=w; ks[L-1]=r.nk; bs[L-1]=buf;
    for(int i=0;i<r.nk;i++){ if(fo<0) fo=r.f[i]; else if(fo!=r.f[i]) pure=false; }
    if(!pure) break;
    int sw=0,W=0; bool bad=false;
    for(int i=0;i<L;i++){ if(ks[i]>0){ if(sw&&sw!=ws[i]) bad=true; sw=ws[i]; } if(ws[i]>W) W=ws[i]; }
    if(bad) break;
    if(sw&&W>sw) continue;
    if((buf&((1<<W)-1))==(b0&((1<<W)-1))){ cy.ok=true; cy.W=W; cy.L=L; cy.fo=fo; cy.M=0; for(int i=0;i<L;i++){ cy.k[i]=ks[i]; cy.M+=ks[i]; cy.fin[i]=bs[i]&((1<<W)-1);} break; }
  }
  return cy.ok?&cy:nullptr;
}

static void process(long p0, Word in){
  if(++depth>maxdepth) maxdepth=depth;
  struct Pkt{ long p; int f; Cnt n; };
  vector<Pkt> Q; for(auto&sg:in) Q.push_back({p0,sg.f,std::move(sg.n)});
  long sg=0;
  while(!Q.empty()){
    if((long)Q.size()>maxq) maxq=Q.size();
    size_t i=Q.size()-1;
    for(;;){
      Pkt&R=Q[i];
      if(R.n.isz()){ Q.erase(Q.begin()+i); break; }
      if(i>0 && Q[i-1].p==R.p && Q[i-1].f==R.f){ cadd(Q[i-1].n,R.n); Q.erase(Q.begin()+i); nmerge++; break; }
      long p=R.p; int f=R.f;
      if(p+2*MAXW>=TSZ/2) die("ANOM tape overflow");
      Cyc*cy=findcycle(f,p);
      int w=0; Rule r; bool have=false;
      if(cy){ w=cy->W; have=true; }
      else if(match(f,win(p,MAXW),w,r)) have=true;
      if(have && i>0 && p+w>Q[i-1].p){ i--; continue; }
      if(!have && i>0){ nflush++; Word ah; long pa=Q[0].p; bool same=true; for(size_t j=0;j<i;j++) if(Q[j].p!=pa) same=false;
        if(same){ for(size_t j=0;j<i;j++) ah.push_back({Q[j].f,std::move(Q[j].n)}); Q.erase(Q.begin(),Q.begin()+i); process(pa,std::move(ah)); }
        else { // complete the packets ahead one position group at a time, front first
          size_t j=0; while(j<i && Q[j].p==pa){ ah.push_back({Q[j].f,std::move(Q[j].n)}); j++; }
          // packets behind the front group may depend on it; run front group alone only if nothing else is ahead of it
          Q.erase(Q.begin(),Q.begin()+j); process(pa,std::move(ah)); }
        break; }
      nbatch++; if((nbatch&0xFFFFF)==0 && maxsec && time(0)-t0>maxsec) die("TIME");
      { long b=R.n.bits(); if(b>maxbits) maxbits=b; if(R.n.t.size()>maxterms) maxterms=R.n.t.size(); }
      if(cy){
        int L=cy->L;
        if(R.n.gt(L)) ncyc++;
        uint32_t rem=cdivmod(R.n,L); int part=0; for(uint32_t k=0;k<rem;k++) part+=cy->k[k];
        cmuladd(R.n,cy->M,part);
        setwin(p,cy->W, rem? cy->fin[rem-1] : cy->fin[L-1]);
        R.p=p+cy->W; R.f=cy->fo<0?f:cy->fo;
        if(cy->M==0||R.n.isz()) Q.erase(Q.begin()+i);
        sg=0; break;
      }
      nsingle++; if(++sg>200000000) die("ANOM no cycle for a long segment");
      if(have){
        setwin(p,w,r.out); R.n.addlow(-1);
        if(r.nk){ vector<Pkt> em; for(int k=0;k<r.nk;k++) em.push_back({p+w,r.f[k],csmall(1)}); Q.insert(Q.begin()+i,em.begin(),em.end()); }
      } else { raw(p,f,false); R.n.addlow(-1); }
      break;
    }
  }
  depth--;
}
static void load(const char*s0){
  string s=s0; bool mir=false; if(s.rfind("m:",0)==0){ mir=true; s=s.substr(2); }
  for(int q=0;q<6;q++) for(int c=0;c<2;c++){ const char*t=s.c_str()+q*7+c*3;
    if(t[0]=='-') tmw[q][c]=-1; else { tmw[q][c]=t[0]-'0'; tmd[q][c]=(t[1]=='R')!=mir?1:-1; tms[q][c]=t[2]-'A'; } }
}
static void autoforms(long nsteps){
  const long SZ=1<<21; static uint8_t tp[1<<21]; long pos=SZ/2; int st=0;
  struct Cand{ int st,d,ctx,ex; long cnt; bool bad; uint8_t*open; };
  vector<Cand> cs; for(int x=0;x<6;x++) for(int d=1;d<=3;d++) for(int cb=0;cb<(1<<(d-1));cb++) cs.push_back({x,d,cb,-1,0,false,(uint8_t*)calloc(SZ,1)});
  for(long n=0;n<nsteps;n++){
    for(auto&c:cs){ if(c.bad) continue;
      long q=pos+c.d;
      if(c.open[q]){ c.open[q]=0; bool ok=true; if(c.ex<0) c.ex=st; else if(c.ex!=st) ok=false; for(int i=0;i<c.d-1;i++) if(tp[q-1-i]!=((c.ctx>>i)&1)) ok=false;
        if(!ok){ c.bad=true; continue; } c.cnt++; }
      if(c.st!=st) continue;
      bool e=true; for(int i=0;i<c.d-1;i++) if(tp[pos-1-i]!=((c.ctx>>i)&1)) e=false;
      if(e) c.open[pos]=1; }
    int c=tp[pos]; if(tmw[st][c]<0) break; tp[pos]=tmw[st][c]; pos+=tmd[st][c]; st=tms[st][c];
    if(pos<8||pos>SZ-8) break;
  }
  printf("cands:"); for(auto&c:cs) if(!c.bad&&c.cnt>=50){ printf(" %c%d",'A'+c.st,c.d); for(int i=0;i<c.d-1;i++) printf("%d",(c.ctx>>i)&1); printf("%c",'A'+c.ex); } printf("\n");
  printf("forms:");
  for(int x=0;x<6;x++){ Cand*best=0; for(auto&c:cs) if(c.st==x&&!c.bad&&c.cnt>=50){ if(!best||c.d<best->d||(c.d==best->d&&c.cnt>best->cnt)) best=&c; }
    if(best){ isform[x]=true; exitst[x]=best->ex; fD[x]=best->d; fctx[x]=best->ctx; printf(" %c%d",'A'+x,best->d); for(int i=0;i<best->d-1;i++) printf("%d",(best->ctx>>i)&1); printf("%c(%ld)",'A'+best->ex,best->cnt); } }
  printf("\n"); for(auto&c:cs) free(c.open);
}
static uint8_t*t0p;
static void checkpoint(long pos,int st){ if(!ckname) return; char nm[300]; snprintf(nm,300,"%s.tmp",ckname); FILE*f=fopen(nm,"wb"); if(!f) return;
  long hdr[6]={topvis,lo,hi,pos,st,(long)(time(0)-t0)}; fwrite(hdr,8,6,f); fwrite(tape+lo,1,hi-lo+1,f); fclose(f); rename(nm,ckname); report("CK"); }
// usage: zvis MACHINE FORMS SOUT run [MAXTOP] [MAXSEC] [CKFILE CKEVERY]   |  zvis MACHINE FORMS SOUT validate R NSTEPS
int main(int argc,char**argv){
  if(argc<5){ fprintf(stderr,"usage\n"); return 2; }
  setvbuf(stdout,0,_IOLBF,0); load(argv[1]); t0p=(uint8_t*)calloc(TSZ,1); tape=t0p+TSZ/2; t0=time(0);
  if(!strcmp(argv[2],"auto")) autoforms(atol(argv[3]));
  else { char*sp=strdup(argv[2]); for(char*g=strtok(sp,",");g;g=strtok(0,",")){ int x=g[0]-'A'; int d=g[1]-'0'; isform[x]=true; fD[x]=d; fctx[x]=0; for(int i=0;i<d-1;i++) fctx[x]|=(g[2+i]-'0')<<i; exitst[x]=g[1+d]-'A'; } }
  string cmd=argv[4];
  if(cmd=="run"){ if(argc>5) maxtop=atol(argv[5]); if(argc>6) maxsec=atol(argv[6]); if(argc>8){ ckname=argv[7]; ckevery=atol(argv[8]); }
    try{ raw(0,0,true); }catch(Stop&){}
    if(argc>9) for(auto&kv:rules){ printf("rule %c w %d in ",'A'+(kv.first>>28),(kv.first>>16)&0xfff); int w=(kv.first>>16)&0xfff; for(int i=0;i<w;i++) printf("%d",(kv.first>>i)&1); printf(" out "); for(int i=0;i<w;i++) printf("%d",(kv.second.out>>i)&1); printf(" subs "); for(int i=0;i<kv.second.nk;i++) printf("%c",'A'+kv.second.f[i]); printf("\n"); }
    return halted?10:0; }
  if(cmd=="validate"){ recmax=atol(argv[5]); long nsteps=atol(argv[6]); maxsec=argc>7?atol(argv[7]):20;
    try{ raw(0,0,true); }catch(Stop&){}
    memset(t0p,0,TSZ); thash=0; long pos=0; int st=0; size_t i=0;
    for(long n=0;n<nsteps && i<recs.size();n++){
      if(isform[st] && pos==recs[i].first && thash==recs[i].second) i++;
      int c=tape[pos]; if(tmw[st][c]<0) break; if(tape[pos]!=tmw[st][c]){ tape[pos]=tmw[st][c]; thash^=zob(pos);} pos+=tmd[st][c]; st=tms[st][c]; }
    printf("VALID %zu of %zu\n",i,recs.size()); return 0; }
  return 2;
}
