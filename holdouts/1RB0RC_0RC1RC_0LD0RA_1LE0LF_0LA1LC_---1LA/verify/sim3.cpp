// Exact accelerated Turing-machine simulator written from scratch for an independent check of
// 1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA  (see README.md).
//
//  Level 1: tape = run-length list of words (<=K cells); a word rule (state, direction, word) is obtained by
//           plain simulation confined to the word; if the head leaves on the far side in the same state the
//           rule is applied to all n copies at once (chain rule).
//  Level 2+: when the tape shape recurs, a rule "shape with counts y -> same shape with counts y+d, for all y
//           in a box (lb<=y<=ub, y = res mod m)" is PROVEN by re-simulating once with symbolic counts
//           (linear forms in the y's).  Every symbolic operation is only performed when it is valid for all
//           admissible y; needed inequalities/congruences are added to the box.  Already proven rules may be
//           used inside a proof (nesting).  A proven rule is applied k times in one jump, k = largest number
//           of applications for which the counts stay inside the box; step total is the exact sum.
//  Nothing is ever applied on the basis of a hash alone: hashes only select candidates.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>
#include <string>
#include <unordered_map>
#include <algorithm>
typedef unsigned long long u64; typedef long long i64; typedef unsigned __int128 u128; typedef __int128 i128;
static int W[6][2],M[6][2],N[6][2];
static void load(const char*spec){for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*p=spec+s*7+b*3; if(p[0]=='-'){N[s][b]=-1;W[s][b]=1;M[s][b]=1;}else{W[s][b]=p[0]-'0';M[s][b]=p[1]=='R'?1:-1;N[s][b]=p[2]-'A';}}}
static std::string s128(i128 x){ if(x==0) return "0"; bool neg=x<0; if(neg)x=-x; std::string r; while(x){r.insert(r.begin(),'0'+(int)(x%10)); x/=10;} if(neg) r.insert(r.begin(),'-'); return r; }
static u128 p128(const char*s){u128 x=0; for(;*s;s++) if(*s>='0'&&*s<='9') x=x*10+(*s-'0'); return x;}
static void die(const char*m){ fprintf(stderr,"FATAL: %s\n",m); exit(9); }
// ---------- exact rationals ----------
static i128 g128(i128 a,i128 b){ if(a<0)a=-a; if(b<0)b=-b; while(b){i128 t=a%b;a=b;b=t;} return a; }
struct Rat{ i128 n,d; Rat(i128 a=0):n(a),d(1){} Rat(i128 a,i128 b){ if(b<0){a=-a;b=-b;} i128 g=g128(a,b); if(g==0)g=1; n=a/g; d=b/g; }
  bool isint()const{return d==1;} bool zero()const{return n==0;} };
static Rat operator+(Rat a,Rat b){ return Rat(a.n*b.d+b.n*a.d,a.d*b.d); }
static Rat operator-(Rat a,Rat b){ return Rat(a.n*b.d-b.n*a.d,a.d*b.d); }
static Rat operator*(Rat a,Rat b){ return Rat(a.n*b.n,a.d*b.d); }
static Rat operator/(Rat a,Rat b){ return Rat(a.n*b.d,a.d*b.n); }
static bool operator==(Rat a,Rat b){ return a.n==b.n&&a.d==b.d; }
static bool operator<(Rat a,Rat b){ return a.n*b.d<b.n*a.d; }
static i128 fdiv(i128 a,i128 b){ i128 q=a/b; if((a%b!=0)&&((a<0)!=(b<0))) q--; return q; }
static i128 rfloor(Rat a){ return fdiv(a.n,a.d); }
static i128 rceil(Rat a){ return -fdiv(-a.n,a.d); }
// ---------- words and word rules ----------
struct Seg{ u64 bits; int len; i64 cnt; };   // leftmost cell = most significant of len bits
struct Rule{ u64 nb; int ns; int xd; u64 t; int halt; };
static std::unordered_map<u64,Rule> memo;
static int K=21;
static const Rule& rule(int st,int d,u64 bits,int len){
  u64 key=(bits<<12)|((u64)len<<4)|((u64)st<<1)|d;
  auto it=memo.find(key); if(it!=memo.end()) return it->second;
  int c[64]; for(int i=0;i<len;i++) c[i]=(bits>>(len-1-i))&1;
  int pos=d?0:len-1; int s=st; u64 t=0; Rule r; r.halt=0;
  while(pos>=0&&pos<len){ int b=c[pos]; if(N[s][b]<0){r.halt=1;break;} c[pos]=W[s][b]; pos+=M[s][b]; s=N[s][b]; t++; if(t>(1ull<<40)) die("in-word loop"); }
  u64 nb=0; for(int i=0;i<len;i++) nb=(nb<<1)|c[i];
  r.nb=nb; r.ns=s; r.xd=pos>=len?1:0; r.t=t; if(r.halt) r.xd=pos;
  return memo.emplace(key,r).first->second;
}
// ---------- symbolic counts ----------
const int MAXV=64; const int MAXT=4;
struct Form{ Rat c; int nv; int v[MAXT]; Rat a[MAXT]; Form():c(0),nv(0){} Form(i128 k):c(k),nv(0){} };
static bool fadd(Form&x,const Form&y,Rat mul=Rat(1)){ x.c=x.c+y.c*mul; for(int j=0;j<y.nv;j++){ int k; for(k=0;k<x.nv;k++) if(x.v[k]==y.v[j]){x.a[k]=x.a[k]+y.a[j]*mul;break;} if(k==x.nv){ if(x.nv==MAXT) return false; x.v[x.nv]=y.v[j]; x.a[x.nv]=y.a[j]*mul; x.nv++; } }
  int w=0; for(int k=0;k<x.nv;k++) if(!x.a[k].zero()){ x.v[w]=x.v[k]; x.a[w]=x.a[k]; w++; } x.nv=w; return true; }
struct SForm{ Rat c; Rat a[MAXV]; bool add(const Form&f,Rat mul=Rat(1)){ c=c+f.c*mul; for(int j=0;j<f.nv;j++) a[f.v[j]]=a[f.v[j]]+f.a[j]*mul; return true; }
  bool onlyvar0()const{ for(int i=1;i<MAXV;i++) if(!a[i].zero()) return false; return true; } };
struct PSeg{ u64 bits; int len; Form f; };
const i64 INF=(i64)4e18;
struct Pat{ u64 bits; int len; int var; i64 val; i64 lb,ub,m,res,d; }; // var<0: exact count val; else variable
struct GRule{ int st,d; std::vector<Pat> pl,pr; bool botL,botR; Rat s0; std::vector<Rat> b; int nvar; int level; u64 uses=0; };
static int CAP=3, SIGD=3, PMAX=400; static i64 CAPV=-1; static u64 SYMBUD=3; static int FIRST=0; static u64 OUTERGAP=4000000; static int VERB=0; static bool NEST=true;
static const char* why=""; static u64 PF[64];
struct Sim{
  std::vector<Seg> L,R; int st=0,d=1; u128 steps=0; u64 macro=0,apps=0,proofs=0,proofok=0,oproofs=0,oproofok=0; int halted=0,haltpos=-1; bool nonhalt=false;
  bool use2=true; int lfirst=0; // length of the first blank word taken on the left (0 = K); only shifts the word grid
  void push(std::vector<Seg>&S,u64 bits,int len,i64 cnt){
    if(cnt==0) return;
    if(S.empty()){ if(bits==0) return; S.push_back({bits,len,cnt}); return; }
    Seg&t=S.back(); if(t.bits==bits&&t.len==len) t.cnt+=cnt; else S.push_back({bits,len,cnt});
  }
  void pushraw(std::vector<Seg>&S,u64 b){ if(!S.empty()&&S.back().len==1&&S.back().bits==b) S.back().cnt++; else S.push_back({b,1,1}); }
  void explode(){ // split one copy of the facing word into single cells (same tape, finer description)
    std::vector<Seg>&F=d?R:L; Seg s; if(F.empty()){ s={0,(d==0&&lfirst)?lfirst:K,1}; if(d==0) lfirst=0; } else { s=F.back(); if(--F.back().cnt==0) F.pop_back(); }
    if(d){ for(int i=s.len-1;i>=0;i--) pushraw(F,(s.bits>>(s.len-1-i))&1); }
    else { for(int i=0;i<s.len;i++) pushraw(F,(s.bits>>(s.len-1-i))&1); }
  }
  // one level-1 macro step. returns 0 stop, 1 normal, 2 reversal
  int step(u128 limit){
    std::vector<Seg>&F=d?R:L; std::vector<Seg>&B=d?L:R;
    bool virt=F.empty(); Seg s= virt? Seg{0,(d==0&&lfirst)?lfirst:K,1} : F.back();
    const Rule& r=rule(st,d,s.bits,s.len);
    if(r.halt){ if(steps+r.t+1>limit){ if(s.len==1) return 0; explode(); return 1; }
      steps+=r.t+1;   // the halting transition is counted as a step
      if(virt&&d==0) lfirst=0;
      if(!virt){ if(--F.back().cnt==0) F.pop_back(); }
      F.push_back({r.nb,s.len,1}); haltpos=r.xd; st=r.ns; halted=1; return 0; }
    u128 room=limit-steps;
    if(r.t>room){ if(s.len==1) return 0; explode(); return 1; }
    macro++; if(virt&&d==0) lfirst=0;
    if(r.xd==d){
      if(r.ns==st){
        if(virt){ fprintf(stderr,"runs away into blank forever (state %c)\n",'A'+st); nonhalt=true; return 0; }
        i64 n=s.cnt; u128 m=room/r.t; if(m<(u128)n) n=(i64)m;
        steps+=(u128)n*r.t; F.back().cnt-=n; if(F.back().cnt==0) F.pop_back();
        push(B,r.nb,s.len,n);
      } else {
        steps+=r.t; if(!virt){ if(--F.back().cnt==0) F.pop_back(); }
        push(B,r.nb,s.len,1); st=r.ns;
      }
      return 1;
    } else {
      steps+=r.t; if(!virt){ if(--F.back().cnt==0) F.pop_back(); }
      push(F,r.nb,s.len,1); st=r.ns; d=!d;
      return 2;
    }
  }
  // ---------- hashes (candidate selection only) ----------
  static inline void mix(u64&h,u64 x){ h^=x; h*=1099511628211ull; h^=h>>29; }
  u64 sig(){
    u64 h=1469598103934665603ull; mix(h,st*2+d);
    for(int side=0;side<2;side++){ std::vector<Seg>&S=side?R:L; int n=S.size();
      for(int j=0;j<SIGD;j++){ if(j>=n){ mix(h,0xdeadbeef+j); break; } const Seg&s=S[n-1-j]; mix(h,s.bits); mix(h,s.len*8+(s.cnt<CAP?s.cnt:CAP)); } mix(h,777); }
    return h;
  }
  u64 fullsig(){
    u64 h=1469598103934665603ull; mix(h,st*2+d);
    for(auto&g:L){mix(h,g.bits);mix(h,g.len*8+(g.cnt<CAP?g.cnt:CAP));} mix(h,999); for(auto&g:R){mix(h,g.bits);mix(h,g.len*8+(g.cnt<CAP?g.cnt:CAP));}
    return h;
  }
  std::unordered_map<u64,std::pair<u64,u64>> seen;      // local sig -> (macro index, epoch)
  std::unordered_map<u64,std::vector<GRule>> rules;     // local sig -> rules
  std::unordered_map<u64,u64> failed;                   // local sig -> failed local proofs
  std::unordered_map<u64,u64> fseen;                    // full sig -> event index
  std::unordered_map<u64,u64> ffailed;
  u64 epoch=0; u64 skip_outer_until=0;
  // ================= symbolic prover =================
  struct Prover{
    Sim&S; std::vector<PSeg> ps[2]; int taken[2]={0,0}; bool bot[2]={false,false}; int nvar=0;
    std::vector<Pat> ip[2]; i64 LB[MAXV],UB[MAXV],MD[MAXV],act[MAXV]; int s,dd; SForm steps; std::vector<Rat> sb; Rat s0; bool quad=false;
    int plfirst; Prover(Sim&S_):S(S_){ plfirst=S.lfirst; s=S.st; dd=S.d; sb.assign(MAXV,Rat(0)); s0=Rat(0); }
    std::vector<Seg>& real(int side){ return side?S.R:S.L; }
    // make sure the proof stack of 'side' has at least n segments (taking untouched real segments from below)
    bool ensure(int side,int n){
      while((int)ps[side].size()<n){
        std::vector<Seg>&RS=real(side); if(taken[side]>=(int)RS.size()) return false;
        const Seg&g=RS[RS.size()-1-taken[side]]; taken[side]++; PSeg q; q.bits=g.bits; q.len=g.len; Pat p; p.bits=g.bits;p.len=g.len;p.lb=1;p.ub=INF;p.m=1;p.res=0;p.d=0;p.val=g.cnt;
        if(g.cnt<(CAPV>0?CAPV:CAP)){ q.f=Form(g.cnt); p.var=-1; }
        else { if(nvar>=MAXV) return false; q.f=Form(0); q.f.nv=1; q.f.v[0]=nvar; q.f.a[0]=Rat(1); p.var=nvar; LB[nvar]=1; UB[nvar]=INF; MD[nvar]=1; act[nvar]=g.cnt; nvar++; }
        ps[side].insert(ps[side].begin(),q); ip[side].push_back(p);
      }
      return true;
    }
    bool exhausted(int side){ return taken[side]>=(int)real(side).size(); }
    Rat eval(const Form&f){ Rat r=f.c; for(int j=0;j<f.nv;j++) r=r+f.a[j]*Rat(act[f.v[j]]); return r; }
    // require f >= v for all admissible y (adds a bound on a single variable if necessary)
    bool require_ge(const Form&f,Rat v){
      if(f.nv==0) return !(f.c<v);
      if(f.nv>1) return false;
      int i=f.v[0]; Rat a=f.a[0]; Rat q=(v-f.c)/a;
      if(Rat(0)<a){ i128 b=rceil(q); if(b>act[i]) return false; if(b>LB[i]) LB[i]=(i64)b; }
      else { i128 b=rfloor(q); if(b<act[i]) return false; if(b<UB[i]) UB[i]=(i64)b; }
      return true;
    }
    // require f == res (mod m) for all admissible y
    bool require_mod(const Form&f,i64 m,i64 res){
      if(m<=1) return true;
      if(f.nv==0){ if(!f.c.isint()) return false; return ((f.c.n-res)%m+m)%m==0; }
      if(f.nv>1||!f.c.isint()||!f.a[0].isint()) return false;
      Rat e=eval(f); if(((e.n-res)%m+m)%m!=0) return false;
      i128 a=f.a[0].n; i128 g=g128(a,m); i64 m2=(i64)(m/g); int i=f.v[0];
      i128 l=(i128)MD[i]/g128(MD[i],m2)*m2; if(l>1000000) return false; MD[i]=(i64)l; return true;
    }
    bool ppush(int side,u64 bits,int len,const Form&f){
      if(f.nv==0&&f.c.zero()) return true;
      if(ps[side].empty()) ensure(side,1);
      if(ps[side].empty()){ if(bits==0&&bot_ok(side)){ return true; } }
      if(!ps[side].empty()&&ps[side].back().bits==bits&&ps[side].back().len==len) return fadd(ps[side].back().f,f);
      PSeg q; q.bits=bits;q.len=len;q.f=f; ps[side].push_back(q); return true;
    }
    bool bot_ok(int side){ if(exhausted(side)){ bot[side]=true; return true; } return false; }
    // one level-1 step on the symbolic configuration. returns 0 fail, 1 normal, 2 reversal
    int pstep(){
      std::vector<PSeg>&F=ps[dd];
      bool virt=false; PSeg g;
      if(F.empty()&&!ensure(dd,1)){ bot[dd]=true; virt=true; g.bits=0; g.len=(dd==0&&plfirst)?plfirst:K; g.f=Form(1); } else g=F.back();
      const Rule& r=rule(s,dd,g.bits,g.len);
      if(r.halt) { why="pstep#1"; return 0; }
      if(r.xd==dd && r.ns==s){
        if(virt) { why="pstep#2"; return 0; }
        F.pop_back(); if(!steps.add(g.f,Rat((i128)r.t))) { why="pstep#3"; return 0; }
        if(!ppush(!dd,r.nb,g.len,g.f)) { why="pstep#4"; return 0; } return 1;
      }
      if(virt&&dd==0) plfirst=0;
      if(!virt){ Form&f=F.back().f;
        if(f.nv==0){ f.c=f.c-Rat(1); if(f.c.zero()) F.pop_back(); }
        else { Form f2=f; f2.c=f2.c-Rat(1);
          if(require_ge(f2,Rat(1))) f=f2;
          else if(f2.nv==1&&eval(f2).zero()){ // the count is exactly 1 at the actual point: pin the variable (lb=ub=actual value); the segment vanishes
            int i=f2.v[0]; if(act[i]<LB[i]||act[i]>UB[i]) { why="pin"; return 0; } LB[i]=UB[i]=act[i]; F.pop_back(); }
          else { why="decrement of a multi-variable count"; return 0; } } }
      steps.c=steps.c+Rat((i128)r.t);
      if(r.xd==dd){ if(!ppush(!dd,r.nb,g.len,Form(1))) { why="pstep#6"; return 0; } s=r.ns; return 1; }
      if(!ppush(dd,r.nb,g.len,Form(1))) { why="pstep#7"; return 0; } s=r.ns; dd=!dd; return 2;
    }
    u64 psig(){
      u64 h=1469598103934665603ull; mix(h,s*2+dd);
      for(int side=0;side<2;side++){ ensure(side,SIGD); int n=ps[side].size();
        for(int j=0;j<SIGD;j++){ if(j>=n){ mix(h,0xdeadbeef+j); break; } const PSeg&q=ps[side][n-1-j]; Rat e=eval(q.f); i64 c=(e<Rat(CAP))?(i64)e.n:CAP; mix(h,q.bits); mix(h,q.len*8+c); } mix(h,777); }
      return h;
    }
    // try to apply proven rule r symbolically. true if applied.
    // dry run: returns the step cost at the actual point of applying r with k reduced by kred, without changing anything
    bool pcost(GRule&r,i128 kred,Rat&cost){ i64 a[MAXV],b[MAXV],c[MAXV]; memcpy(a,LB,sizeof a); memcpy(b,UB,sizeof b); memcpy(c,MD,sizeof c); bool q=quad;
      bool ok=papply(r,kred,true,&cost); memcpy(LB,a,sizeof a); memcpy(UB,b,sizeof b); memcpy(MD,c,sizeof c); quad=q; return ok; }
    bool papply(GRule&r,i128 kred=0,bool dry=false,Rat*cost=nullptr){
      if(r.st!=s||r.d!=dd) { PF[1]++; return false; }
      std::vector<Pat>* rp[2]={&r.pl,&r.pr}; bool rb[2]={r.botL,r.botR};
      for(int side=0;side<2;side++){ int n=rp[side]->size(); ensure(side,n); if((int)ps[side].size()<n) { PF[2]++; return false; }
        if(rb[side]){ if((int)ps[side].size()!=n||!exhausted(side)) { PF[3]++; return false; } } }
      // concrete pre-check (so that committed constraints always contain the actual point)
      Form* fv[MAXV]; const Pat* pv[MAXV];
      for(int side=0;side<2;side++){ int n=rp[side]->size(); for(int j=0;j<n;j++){ PSeg&q=ps[side][ps[side].size()-1-j]; const Pat&p=(*rp[side])[j];
          if(q.bits!=p.bits||q.len!=p.len) { PF[4]++; return false; } Rat e=eval(q.f); if(!e.isint()) { PF[5]++; return false; }
          if(p.var<0){ if(q.f.nv!=0||!(q.f.c==Rat(p.val))) { PF[6]++; return false; } }
          else { if(e.n<p.lb||e.n>p.ub) { PF[7]++; return false; } if(p.m>1&&((e.n-p.res)%p.m+p.m)%p.m!=0) { PF[8]++; return false; } fv[p.var]=&q.f; pv[p.var]=&p; } } }
      // limiting variable (concretely)
      int jstar=-1; i128 kact=-1;
      for(int v=0;v<r.nvar;v++){ const Pat&p=*pv[v]; i128 e=eval(*fv[v]).n; i128 kk=-1;
        if(p.d<0) kk=(e-p.lb)/(-p.d)+1; else if(p.d>0&&p.ub<INF) kk=(p.ub-e)/p.d+1;
        if(kk>=0&&(kact<0||kk<kact)){ kact=kk; jstar=v; } }
      if(jstar<0) { PF[9]++; return false; }
      // commit pattern constraints
      for(int v=0;v<r.nvar;v++){ const Pat&p=*pv[v]; if(!require_ge(*fv[v],Rat(p.lb))) { PF[10]++; return false; }
        if(p.ub<INF){ Form neg; if(!fadd(neg,*fv[v],Rat(-1))) { PF[11]++; return false; } if(!require_ge(neg,Rat(-(i128)p.ub))) { PF[12]++; return false; } }
        if(!require_mod(*fv[v],p.m,p.res)) { PF[13]++; return false; } }
      // k as a form: k = floor(num/D)+1, num = f-lb (d<0) or ub-f (d>0)
      Form kf; { const Pat&p=*pv[jstar]; Form num; i64 D;
        if(p.d<0){ num=*fv[jstar]; num.c=num.c-Rat(p.lb); D=-p.d; } else { if(!fadd(num,*fv[jstar],Rat(-1))) { PF[14]++; return false; } num.c=num.c+Rat(p.ub); D=p.d; }
        Rat e=eval(num); i64 rho=(i64)(((e.n%D)+D)%D);
        if(!require_mod(num,D,rho)) { PF[15]++; return false; }
        num.c=num.c-Rat(rho); if(!fadd(kf,num,Rat(1,D))) { PF[16]++; return false; } kf.c=kf.c+Rat(1); }
      if(kred>0){ kf.c=kf.c-Rat(kred); if(!require_ge(kf,Rat(1))) { PF[40]++; return false; } }   // fewer applications are always valid
      // all other limits must allow k applications
      for(int v=0;v<r.nvar;v++){ if(v==jstar) continue; const Pat&p=*pv[v];
        Form g=*fv[v]; Form km1=kf; km1.c=km1.c-Rat(1); if(!fadd(g,km1,Rat(p.d))) { PF[17]++; return false; }
        if(p.d<0){ g.c=g.c-Rat(p.lb); if(!require_ge(g,Rat(0))) { PF[18]++; return false; } }
        else if(p.d>0&&p.ub<INF){ Form ng; if(!fadd(ng,g,Rat(-1))) { PF[19]++; return false; } ng.c=ng.c+Rat(p.ub); if(!require_ge(ng,Rat(0))) { PF[20]++; return false; } } }
      // steps: k*s0 + sum b_v (k f_v + d_v k(k-1)/2)
      SForm ds;
      if(kf.nv==0){ Rat k=kf.c; ds.c=ds.c+k*r.s0;
        for(int v=0;v<r.nvar;v++) if(!r.b[v].zero()){ ds.add(*fv[v],r.b[v]*k); ds.c=ds.c+r.b[v]*Rat(pv[v]->d)*k*(k-Rat(1))/Rat(2); } }
      else { Rat per=r.s0;   // k is symbolic: only step forms that stay linear are accepted
        for(int v=0;v<r.nvar;v++) if(!r.b[v].zero()) { if(fv[v]->nv!=0||pv[v]->d!=0){ quad=true; PF[41]++; return false; } per=per+r.b[v]*fv[v]->c; }
        ds.add(kf,per); }
      if(dry){ Rat e=ds.c; for(int v=0;v<nvar;v++) e=e+ds.a[v]*Rat(act[v]); *cost=e; return true; }
      steps.c=steps.c+ds.c; for(int v=0;v<MAXV;v++) steps.a[v]=steps.a[v]+ds.a[v];
      // new counts
      for(int v=0;v<r.nvar;v++) if(pv[v]->d!=0){ if(!fadd(*fv[v],kf,Rat(pv[v]->d))) { PF[22]++; return false; } }
      // renormalise the touched part of the stacks (zero counts vanish, equal neighbours merge)
      for(int side=0;side<2;side++){ int n=rp[side]->size(); std::vector<PSeg> tmp(ps[side].end()-n,ps[side].end()); ps[side].resize(ps[side].size()-n);
        for(auto&q:tmp){ if(q.f.nv==0&&q.f.c.zero()) continue; if(!ps[side].empty()&&ps[side].back().bits==q.bits&&ps[side].back().len==q.len){ if(!fadd(ps[side].back().f,q.f)) { PF[23]++; return false; } } else ps[side].push_back(q); } }
      return true;
    }
    // does the symbolic configuration equal the initial shape with shifted counts?  fills deltas.
    bool closed(){
      if(s!=S.st||dd!=S.d) return false;
      for(int side=0;side<2;side++){
        std::vector<PSeg>&q=ps[side]; size_t lo=0; if(bot[side]){ while(lo<q.size()&&q[lo].bits==0&&q[lo].f.nv==0) lo++; }
        if(q.size()-lo!=ip[side].size()) return false;
        for(size_t j=0;j<ip[side].size();j++){ PSeg&g=q[q.size()-1-j]; Pat&p=ip[side][j];
          if(g.bits!=p.bits||g.len!=p.len) return false;
          if(p.var<0){ if(g.f.nv!=0||!(g.f.c==Rat(p.val))) return false; }
          else if(LB[p.var]==UB[p.var]){ // pinned variable: its count is a known number; accept any form made of pinned variables only
            for(int t=0;t<g.f.nv;t++) if(LB[g.f.v[t]]!=UB[g.f.v[t]]) return false; Rat e=eval(g.f); if(!e.isint()) return false; p.d=(i64)(e.n-act[p.var]); }
          else { if(g.f.nv!=1||g.f.v[0]!=p.var||!(g.f.a[0]==Rat(1))||!g.f.c.isint()) return false; p.d=(i64)g.f.c.n; } } }
      return true;
    }
  };
  // local==true : exactly P level-1 steps, no nested rules.  local==false: nested rules allowed, run until closure.
  bool prove(bool local,u64 P,GRule&out){
    Prover pr(*this); u64 ev=0; int closures=0; bool ok=false;
    if(local){
      for(u64 it=0;it<P;it++) if(!pr.pstep()) return false;
      if(!pr.closed()) return false; ok=true;
    } else {
      bool chk=true;
      while(ev<P){
        if(chk){
          if(ev>0&&pr.closed()){
            closures++; bool resok=true;
            for(int side=0;side<2;side++) for(auto&p:pr.ip[side]) if(p.var>=0&&pr.MD[p.var]>1&&(p.d%pr.MD[p.var])!=0) resok=false;
            if(resok){ ok=true; break; }
            if(closures>=12){ why="residues never close"; return false; }
          }
          u64 h=pr.psig(); auto ir=rules.find(h); bool ap=false;
          if(ir!=rules.end()) for(auto&r:ir->second){ if(pr.papply(r)){ ap=true; break; } }
          if(ap){ ev++; continue; }
        }
        int rc=pr.pstep(); if(!rc) return false; ev++; chk=(rc==2);
      }
      if(!ok){ why=pr.quad?"budget (quadratic step term refused)":"budget"; 
      }
      if(!ok) return false;
    }
    out.st=st; out.d=d; out.botL=pr.bot[0]; out.botR=pr.bot[1]; out.nvar=pr.nvar; out.b.assign(pr.nvar,Rat(0)); out.level=local?2:3;
    bool lim=false;
    for(int side=0;side<2;side++) for(auto&p:pr.ip[side]) if(p.var>=0){ int v=p.var;
      i64 lb=pr.LB[v]; if(1-p.d>lb) lb=1-p.d;   // counts after an application are again >= 1
      p.lb=lb; p.ub=pr.UB[v]; p.m=pr.MD[v]; p.res=((pr.act[v]%p.m)+p.m)%p.m;
      if(pr.act[v]<p.lb||pr.act[v]>p.ub) return false;
      if(p.d<0||(p.d>0&&p.ub<INF)) lim=true; }
    for(int j=0;j<pr.nvar;j++) out.b[j]=pr.steps.a[j];
    out.s0=pr.steps.c; out.pl=pr.ip[0]; out.pr=pr.ip[1];
    // the step form must be positive at the actual point
    Rat e=pr.steps.c; for(int j=0;j<pr.nvar;j++) e=e+pr.steps.a[j]*Rat(pr.act[j]); if(!(Rat(0)<e)) return false;
    if(!lim){ // no count ever leaves the box: the shape recurs forever
      bool grows=false; for(int side=0;side<2;side++) for(auto&p:out.pl) (void)p;
      fprintf(stderr,"PROVEN NON-HALTING: rule with no limiting count (level %d)\n",out.level); nonhalt=true; }
    return true;
  }
  // Symbolic run from the current (initial) configuration, counts >= CAPV free, using the rules already proven.
  // Stops when the configuration is of C-form (state E, head on a blank cell with only blanks to its left, next cell 1)
  // and the symbolic step count equals T0 + T1*(y - y_actual).  Prints the final tape with symbolic counts.
  bool symrun(u64 budget,i128 T0,i128 T1,FILE*f){
    Prover pr(*this); bool chk=true; u64 ev=0;
    while(ev<budget){
      if(pr.steps.onlyvar0()&&pr.nvar<=1){
        Rat a=pr.steps.a[0]; i64 ya=pr.nvar?pr.act[0]:0; Rat remr=Rat(T0)-(pr.steps.c+a*Rat(ya));
        if(a==Rat(T1)&&remr.isint()&&remr.n<0){ fprintf(f,"symbolic run: passed the target time by %s steps (inside a jump)\n",s128(-remr.n).c_str()); return false; }
        if(Rat(T1)<a){ fprintf(f,"symbolic run: y-coefficient of the step count exceeded the target's\n"); return false; }
        if(a==Rat(T1)&&remr.isint()&&remr.n<=20000){
          // finish the last remr steps cell by cell inside a window made of constant-count words only
          i64 rem=(i64)remr.n; std::vector<int> cl,cr; bool leftblank=false;
          while((i64)cl.size()<rem+2){ if(pr.ps[0].empty()&&!pr.ensure(0,1)){ leftblank=true; break; } PSeg&q=pr.ps[0].back(); if(q.f.nv) break; 
            for(int j=q.len-1;j>=0;j--) cl.push_back((q.bits>>(q.len-1-j))&1); q.f.c=q.f.c-Rat(1); if(q.f.c.zero()) pr.ps[0].pop_back(); }
          if(leftblank) while((i64)cl.size()<rem+2) cl.push_back(0);
          while((i64)cr.size()<rem+2){ if(pr.ps[1].empty()&&!pr.ensure(1,1)) break; PSeg&q=pr.ps[1].back(); if(q.f.nv) break;
            for(int j=0;j<q.len;j++) cr.push_back((q.bits>>(q.len-1-j))&1); q.f.c=q.f.c-Rat(1); if(q.f.c.zero()) pr.ps[1].pop_back(); }
          std::vector<int> c(cl.rbegin(),cl.rend()); long pos=pr.dd?(long)c.size():(long)c.size()-1; c.insert(c.end(),cr.begin(),cr.end());
          int s2=pr.s; bool okw=true;
          for(i64 t=0;t<rem;t++){ if(pos<0||pos>=(long)c.size()){okw=false;break;} int bb=c[pos]; if(N[s2][bb]<0){okw=false;break;} c[pos]=W[s2][bb]; pos+=M[s2][bb]; s2=N[s2][bb]; }
          if(!okw||pos<0||pos+1>=(long)c.size()){ fprintf(f,"symbolic run: final cell-level window left or halted\n"); return false; }
          bool cf=(s2==4)&&leftblank&&pr.ps[0].empty()&&c[pos+1]==1; for(long i=0;i<=pos;i++) if(c[i]) cf=false;
          if(!cf){ fprintf(f,"symbolic run: at the target time the configuration is not of C-form (state %c)\n",'A'+s2); return false; }
          fprintf(f,"SYMBOLIC TARGET REACHED after %llu events (+%lld final single steps); free variables %d\n",ev,rem,pr.nvar);
          for(int v=0;v<pr.nvar;v++) fprintf(f,"box: y (number of copies of the free word; actual %lld) : %lld <= y <= %s , y = %lld (mod %lld)\n",pr.act[v],pr.LB[v],pr.UB[v]>=INF?"inf":s128(pr.UB[v]).c_str(),pr.act[v]%pr.MD[v],pr.MD[v]);
          fprintf(f,"steps = %s + %s*y\n",s128(T0-T1*(i128)ya).c_str(),s128(T1).c_str());
          fprintf(f,"symtape: 0^1 "); for(long i=pos+1;i<(long)c.size();i++) fputc('0'+c[i],f); fprintf(f,"^1");
          for(size_t i=pr.ps[1].size();i-->0;){ PSeg&q=pr.ps[1][i]; fputc(' ',f); for(int j=0;j<q.len;j++) fputc('0'+((q.bits>>(q.len-1-j))&1),f);
            if(q.f.nv==0) fprintf(f,"^%s",s128(q.f.c.n).c_str()); else { if(!q.f.c.isint()||!q.f.a[0].isint()) fprintf(f,"^NONINT"); else fprintf(f,"^(%s+%s*y)",s128(q.f.c.n).c_str(),s128(q.f.a[0].n).c_str()); } }
          for(int i=(int)R.size()-1-pr.taken[1];i>=0;i--){ Seg&q=R[i]; fputc(' ',f); for(int j=0;j<q.len;j++) fputc('0'+((q.bits>>(q.len-1-j))&1),f); fprintf(f,"^%lld",q.cnt); }
          fprintf(f,"\n"); return true; } }
      if(chk){ u64 h=pr.psig(); auto ir=rules.find(h); bool ap=false;
        Rat now=pr.steps.c; for(int v=0;v<pr.nvar;v++) now=now+pr.steps.a[v]*Rat(pr.act[v]); Rat room=Rat(T0)-now;
        if(ir!=rules.end()) for(auto&r:ir->second){ Rat cost;
          if(!pr.pcost(r,0,cost)) continue;
          if(!(room<cost)){ if(pr.papply(r)){ ap=true; break; } continue; }
          // would pass the target time: apply fewer times (largest number that still fits at the actual point)
          i128 lo=0,hi=1; bool fit=false;
          while(hi<((i128)1<<100)){ if(!pr.pcost(r,hi,cost)) break; if(!(room<cost)){ fit=true; break; } lo=hi; hi*=2; }
          if(!fit) continue;
          while(hi-lo>1){ i128 m=lo+(hi-lo)/2; if(pr.pcost(r,m,cost)&&!(room<cost)) hi=m; else lo=m; }
          if(pr.papply(r,hi)){ ap=true; break; } }
        if(ap){ ev++; continue; } }
      int rc=pr.pstep(); if(!rc){ fprintf(f,"symbolic run failed: %s (events %llu)\n",why,ev); return false; } ev++; chk=(rc==2);
    }
    fprintf(f,"symbolic run: budget exhausted (%s)\n",pr.quad?"a quadratic step term was refused":"-"); for(int i=0;i<64;i++) if(PF[i]) fprintf(f,"  papply refusal #%d: %llu\n",i,PF[i]);
    for(int v=0;v<pr.nvar;v++) fprintf(f,"  box so far: y actual %lld : %lld <= y <= %s , modulus %lld\n",pr.act[v],pr.LB[v],pr.UB[v]>=INF?"inf":s128(pr.UB[v]).c_str(),pr.MD[v]);
    fprintf(f,"  steps so far %s + %s*y ; psteps %llu\n",s128(pr.steps.c.n).c_str(),s128(pr.steps.a[0].n).c_str(),ev); return false;
  }
  // apply a proven rule to the concrete tape as often as possible (bounded by the step limit)
  bool apply(GRule&r,u128 limit){
    if(r.st!=st||r.d!=d) return false;
    if(r.pl.size()>L.size()||r.pr.size()>R.size()) return false;
    if(r.botL&&r.pl.size()!=L.size()) return false;
    if(r.botR&&r.pr.size()!=R.size()) return false;
    i64 k=-1; i64 y[MAXV];
    for(int side=0;side<2;side++){ std::vector<Seg>&S=side?R:L; std::vector<Pat>&ip=side?r.pr:r.pl;
      for(size_t j=0;j<ip.size();j++){ const Seg&g=S[S.size()-1-j]; const Pat&p=ip[j];
        if(g.bits!=p.bits||g.len!=p.len) return false;
        if(p.var<0){ if(g.cnt!=p.val) return false; }
        else { if(g.cnt<p.lb||g.cnt>p.ub) return false; if(p.m>1&&(g.cnt%p.m)!=p.res) return false; y[p.var]=g.cnt;
          i64 kk=-1; if(p.d<0) kk=(g.cnt-p.lb)/(-p.d)+1; else if(p.d>0&&p.ub<INF) kk=(p.ub-g.cnt)/p.d+1;
          if(kk>=0&&(k<0||kk<k)) k=kk; } } }
    if(k<0){ nonhalt=true; fprintf(stderr,"rule with no limiting count applies: never halts\n"); return false; }
    auto tot=[&](i64 kk)->u128{ Rat t=Rat(kk)*r.s0;
      for(int side=0;side<2;side++){ std::vector<Pat>&ip=side?r.pr:r.pl; for(auto&p:ip) if(p.var>=0&&!r.b[p.var].zero()){ i128 sum=(i128)kk*y[p.var]+(i128)p.d*((i128)kk*(kk-1)/2); t=t+r.b[p.var]*Rat(sum); } }
      if(!t.isint()||t.n<=0) die("non-integer or non-positive step total in rule application"); return (u128)t.n; };
    u128 room=limit-steps;
    if(tot(k)>room){ i64 lo=0,hi=k; while(hi-lo>1){ i64 m=lo+(hi-lo)/2; if(tot(m)<=room) lo=m; else hi=m; } k=lo; if(k==0) return false; }
    steps+=tot(k); apps++; r.uses++;
    for(int side=0;side<2;side++){ std::vector<Seg>&S=side?R:L; std::vector<Pat>&ip=side?r.pr:r.pl;
      std::vector<Seg> tmp(S.end()-ip.size(),S.end()); S.resize(S.size()-ip.size());
      for(size_t j=ip.size();j-->0;){ const Pat&p=ip[j]; Seg g=tmp[tmp.size()-1-j]; if(p.var>=0) g.cnt+=k*p.d; if(g.cnt<0) die("negative count"); push(S,g.bits,g.len,g.cnt); } }
    if(VERB>=2||(VERB>=1&&r.level>=3)) fprintf(stderr,"apply L%d rule k=%lld steps=%s macro=%llu apps=%llu segs=%zu+%zu\n",r.level,k,s128(steps).c_str(),macro,apps,L.size(),R.size());
    return true;
  }
  void run(u128 T){
    int chk=0; // 0 none, 2 after reversal, 3 after rule application
    while(steps<T && !nonhalt){
      if(chk && use2){
        u64 h=sig(); bool ap=false;
        auto ir=rules.find(h);
        if(ir!=rules.end()){ for(auto&r:ir->second){ if(apply(r,T)){ap=true;break;} if(nonhalt) return; } }
        if(!ap && chk==2){
          auto is=seen.find(h);
          if(is!=seen.end() && is->second.second==epoch && macro-is->second.first<=(u64)PMAX){
            u64 P=macro-is->second.first; u64&fc=failed[h];
            if(fc<8){ GRule r; proofs++; if(prove(true,P,r)){ proofok++; rules[h].push_back(r); if(nonhalt) return; if(apply(rules[h].back(),T)) ap=true; } else fc++; }
          }
          if(!ap){ seen[h]={macro,epoch}; if(seen.size()>4000000) seen.clear(); }
        }
        if(!ap && chk==3 && NEST){
          u64 fh=fullsig(); u64 ev=macro+apps; auto it=fseen.find(fh);
          if(it!=fseen.end() && ev-it->second<=OUTERGAP && ev>=skip_outer_until){
            u64 gap=ev-it->second; u64&fc=ffailed[fh];
            if(fc<3){ GRule r; oproofs++; if(prove(false,3*gap+200,r)){ oproofok++; rules[h].push_back(r); if(nonhalt) return;
                if(VERB>=1) fprintf(stderr,"outer rule proven: gap %llu events, nvar %d, depth %zu+%zu\n",gap,r.nvar,r.pl.size(),r.pr.size());
                if(apply(rules[h].back(),T)) ap=true; }
              else { fc++; skip_outer_until=ev+2*gap; if(VERB>=1) fprintf(stderr,"outer proof failed (gap %llu): %s\n",gap,why); } }
          }
          if(!ap){ fseen[fh]=ev; if(fseen.size()>4000000) fseen.clear(); }
        }
        if(ap){ epoch++; chk=3; continue; }
      }
      int rc=step(T);
      if(VERB>=1&&(macro&((1<<24)-1))==0) fprintf(stderr,"progress macro=%llu apps=%llu steps=%s segs=%zu+%zu oproofs=%llu/%llu\n",macro,apps,s128(steps).c_str(),L.size(),R.size(),oproofok,oproofs);
      if(rc==0) break;
      chk=(rc==2)?2:0;
    }
  }
  void dump(FILE*f){
    fprintf(f,"steps %s state %c dir %c halted %d haltpos %d nonhalt %d\n",s128(steps).c_str(),'A'+st,d?'R':'L',halted,haltpos,(int)nonhalt);
    auto pr=[&](const Seg&s){ for(int i=0;i<s.len;i++) fputc('0'+((s.bits>>(s.len-1-i))&1),f); fprintf(f,"^%lld ",s.cnt); };
    for(size_t i=0;i<L.size();i++) pr(L[i]);
    fprintf(f,"\n%c%c\n",d?'>':'<','A'+st);
    for(size_t i=R.size();i-->0;) pr(R[i]);
    fprintf(f,"\n");
  }
  // tape = desc to the right of the head (head on first cell of desc), blank elsewhere
  void build_right(const std::vector<std::pair<std::string,i64>>&desc){
    std::vector<Seg> out; std::string buf;
    auto emit=[&](u64 b,int l,i64 c){ if(!out.empty()&&out.back().bits==b&&out.back().len==l) out.back().cnt+=c; else out.push_back({b,l,c}); };
    bool first=FIRST>0;
    auto flush=[&](bool fin){ while((int)buf.size()>=(first?FIRST:K)||(fin&&!buf.empty())){ int l=std::min((int)buf.size(),first?FIRST:K); first=false; u64 b=0; for(int i=0;i<l;i++) b=(b<<1)|(buf[i]-'0'); emit(b,l,1); buf.erase(0,l);} };
    for(auto&pr:desc){ const std::string&w=pr.first; i64 n=pr.second; int wl=w.size();
      int P=1; while((wl*P)%K) P++;
      while(n>0){
        if(!first&&n>=3*P&&(wl*P)==K){ // buf + w^P = one block + buf again (periodicity): emit many blocks at once
          std::string big=buf; for(int i=0;i<P;i++) big+=w; std::string blk=big.substr(0,K); std::string rest=big.substr(K);
          if(rest==buf){ u64 b=0; for(int i=0;i<K;i++) b=(b<<1)|(blk[i]-'0'); i64 reps=n/P-1; emit(b,K,reps); n-=reps*P; continue; } }
        buf+=w; n--; flush(false);
      }
    }
    flush(true);
    R.clear(); for(size_t i=out.size();i-->0;) R.push_back(out[i]);
    while(!R.empty()&&R[0].bits==0) R.erase(R.begin());
  }
};
int main(int argc,char**argv){
  load("1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA");
  // usage: sim3 [-1] [-nonest] [-v N] [-k K] [-cap C] [-sigd D] [-pmax P] T [STATE word^n ...]
  Sim S; int ai=1; bool SYM=false; int LF=0; i64 CAPVSYM=0; i128 T1SYM=0;
  while(ai<argc&&argv[ai][0]=='-'){ std::string o=argv[ai];
    if(o=="-1"){S.use2=false;ai++;} else if(o=="-nonest"){NEST=false;ai++;} else if(o=="-v"){VERB=atoi(argv[ai+1]);ai+=2;} else if(o=="-k"){K=atoi(argv[ai+1]);ai+=2;} else if(o=="-cap"){CAP=atoi(argv[ai+1]);ai+=2;} else if(o=="-sigd"){SIGD=atoi(argv[ai+1]);ai+=2;} else if(o=="-pmax"){PMAX=atoi(argv[ai+1]);ai+=2;} else if(o=="-first"){FIRST=atoi(argv[ai+1]);ai+=2;} else if(o=="-lfirst"){LF=atoi(argv[ai+1]);ai+=2;} else if(o=="-sym"){SYM=true;CAPVSYM=atoll(argv[ai+1]);T1SYM=(i128)p128(argv[ai+2]);ai+=3;} else if(o=="-gap"){OUTERGAP=atoll(argv[ai+1]);ai+=2;} else break; }
  u128 T=p128(argv[ai++]);
  if(ai<argc){ S.st=argv[ai++][0]-'A'; std::vector<std::pair<std::string,i64>> desc; for(int i=ai;i<argc;i++){ std::string a=argv[i]; size_t p=a.find('^'); if(p==std::string::npos) desc.push_back({a,1}); else desc.push_back({a.substr(0,p),atoll(a.c_str()+p+1)}); } S.build_right(desc); }
  S.lfirst=LF; std::vector<Seg> R0=S.R; int st0=S.st;
  S.run(T);
  S.dump(stdout);
  if(SYM){ // concrete run above has populated the rule table and ended exactly at step T; now redo it with a free count
    bool cform=(S.st==4&&S.d==0&&S.L.empty()&&!S.R.empty()&&((S.R.back().bits>>(S.R.back().len-1))&1));
    cform=true;
    u64 budget=SYMBUD*(S.macro+S.apps)+1000;
    if(cform){ S.lfirst=LF; S.L.clear(); S.R=R0; S.st=st0; S.d=1; CAPV=CAPVSYM; memset(PF,0,sizeof PF); S.symrun(budget,(i128)T,T1SYM,stdout); } }
  size_t nr=0,n3=0; for(auto&kv:S.rules){ nr+=kv.second.size(); for(auto&r:kv.second) if(r.level>=3) n3++; }
  fprintf(stderr,"macro %llu apps %llu | word rules %zu | local proofs %llu ok %llu | outer proofs %llu ok %llu | rules %zu (outer %zu)\n",S.macro,S.apps,memo.size(),S.proofs,S.proofok,S.oproofs,S.oproofok,nr,n3);
}
