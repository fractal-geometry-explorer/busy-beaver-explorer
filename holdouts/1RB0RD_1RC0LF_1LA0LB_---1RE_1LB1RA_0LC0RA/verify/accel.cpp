// accel.cpp: exact accelerated Turing-machine simulator, written from scratch for an independent check of the
// closed-set certificate of 1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA (see README.md).  It shares no code
// with py/closure/.
//
// Tape = left stack of runs (word of K cells, count), one "back" block of K cells directly behind the head,
// right stack of runs; everything beyond the stacks is blank.  The head stands at a block boundary, the back
// block behind it, facing the top block of the stack in front (dir 1 = right, 0 = left).
//
// Level 1 (block step / chain step).  rule(state, dir, back, word): plain simulation confined to the 2K cells
//   [back][word] (mirror image for dir 0), head starting on the near cell of word, until the head leaves the
//   window (or halts).  Leaving in front: the old back block (as modified) is pushed behind, the modified word
//   becomes the back block.  Leaving behind: the direction flips, the modified word is pushed, the modified back
//   stays the back block.  If the head leaves in front in the same state and the new back block equals the old
//   one, the same happens on every further copy of the word, so a whole run is crossed at once
//   (steps = t * count) [chain step].
//   Whenever nothing non-blank lies to the left of the window (left stack empty after taking the block), the
//   window is simulated cell by cell without the rule table, one block only, and at every cell step the
//   "node" test is made: state A, everything to the left of the head blank, cells from the head on =
//   01001000...  (no chain step is ever taken there, so no node can be skipped at level 1).
//
// Level 2 (cycle jump).  At "snapshot moments" (head about to enter the leftmost block from the right) the
//   configuration is stored under its shape = (state, words, exact counts of all runs with count < BIG, a
//   marker for the others).  When the same shape recurs, the stretch between the two snapshots is RE-SIMULATED
//   from the stored snapshot with every big count n_v carried as "variable v + offset".  Every decision of the
//   engine in that re-simulation depends only on the shape, provided every variable run keeps a count >= 2
//   at all times; the least offset seen gives the condition n_v >= base_v = 2 - minoff_v.  If the re-simulation
//   ends in the same shape with counts n_v + d_v (and it met no node test prefix, no halt, no merge of two
//   variable runs), then this is a proven rule:
//        shape(n) -> shape(n + d) in s0 + sum_v sv*n_v steps, with no halt and no node, whenever n >= base.
//   It is applied N times in one jump, N = the largest number such that n + r d >= base for r = 0..N-1,
//   with the exact step total N*s(n) + sum_v sv*d_v*N(N-1)/2.  Nothing is applied on the basis of a
//   hash: shapes are compared exactly (they are the map key), and the re-simulated end configuration is
//   asserted equal to the real current one (counts, steps, operation count).
//
// usage: accel [-K k] [-big n] [-minB b] [-maxops n] [-nojump] MACHINE < input
//   input lines: "blank"  or  "B T"   (start: state A on the first cell of 01001000 (01)^B T; T may be "-")
//   output per line: every node met at a step > 0 as "NODE steps B T", stopping at the first with B >= minB;
//   or "HALT steps" (steps executed before the undefined transition is met); or "INF reason"; or "LIMIT".
//   A final "# ops=.. jumps=.. reps=.." line gives statistics.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#include <map>
#include <unordered_map>
#include <iostream>
#include <sstream>
typedef long long i64; typedef __int128 i128; typedef unsigned long long u64;
static int K=6; static i64 BIG=64; static i64 MINB=0; static i64 MAXOPS=2000000000LL; static bool NOJUMP=false;
static int W[6][2],M[6][2],NX[6][2];
static void die(const char*m){ fprintf(stderr,"FATAL: %s\n",m); printf("FATAL %s\n",m); exit(9); }
static std::string s128(i128 x){ if(x==0) return "0"; bool neg=x<0; if(neg)x=-x; std::string r; while(x>0){r.insert(r.begin(),(char)('0'+(int)(x%10))); x/=10;} if(neg) r.insert(r.begin(),'-'); return r; }

struct Rule{ u64 nb,nw; int st; int xdir; i64 t; int halt; };   // halt: 0 none, 1 halts after t steps, 2 step limit inside the window
static const i64 INLIMIT=20000000;
// window cells: dir 1: [back][w], head at index K;  dir 0: [w][back], head at index K-1
static void fill(int*c,int dir,u64 back,u64 w){ u64 a=dir?back:w, b=dir?w:back; for(int i=0;i<K;i++){ c[i]=(int)((a>>(K-1-i))&1); c[K+i]=(int)((b>>(K-1-i))&1); } }
static void unfill(const int*c,int dir,u64&nb,u64&nw){ u64 a=0,b=0; for(int i=0;i<K;i++){ a=(a<<1)|(u64)c[i]; b=(b<<1)|(u64)c[K+i]; } if(dir){nb=a;nw=b;}else{nw=a;nb=b;} }
static std::unordered_map<u64,Rule> memo;
static const Rule& rule(int st,int dir,u64 back,u64 w){
  u64 key=(((back<<K)|w)<<4)|((u64)st<<1)|(u64)dir;
  auto it=memo.find(key); if(it!=memo.end()) return it->second;
  int c[64]; fill(c,dir,back,w);
  int pos=dir?K:K-1, s=st; i64 t=0; Rule r; r.halt=0;
  while(pos>=0&&pos<2*K){ int b=c[pos]; if(NX[s][b]<0){r.halt=1;break;} c[pos]=W[s][b]; pos+=M[s][b]; s=NX[s][b]; t++;
    if(t>INLIMIT){ r.halt=2; break; } }
  unfill(c,dir,r.nb,r.nw); r.st=s; r.xdir=pos>=2*K?1:0; r.t=t;
  return memo.emplace(key,r).first->second;
}

struct Run{ u64 w; i64 n; int var; i64 off; };   // var >= 0 (tracking only): n = value(var) + off
enum Status{RUN,NODE,HALT,INF,LIMIT};
struct Snap{ std::vector<Run> L,R; u64 back; int st,dir; i128 steps; i64 ops; };

struct Eng{
  std::vector<Run> L,R; u64 back=0; int st=0,dir=1; i128 steps=0; i64 ops=0;
  Status status=RUN; std::string info;
  bool track=false; const char*fail=nullptr; std::vector<i64> minoff; i128 s0=0; std::vector<i128> sv;
  i64 jumps=0; i128 reps=0;
  std::vector<std::string> out;

  void note(const Run&r){ if(track&&r.var>=0){ if(r.off<minoff[r.var]) minoff[r.var]=r.off; if(r.n<2) fail="variable run below 2"; } }
  void addSteps(i64 t,const Run&mv){ steps+=(i128)t*mv.n; if(track){ if(mv.var>=0){ s0+=(i128)t*mv.off; sv[mv.var]+=t; } else s0+=(i128)t*mv.n; } }
  // remove blocks from the top run of F: mode 0 = one block, 1 = the whole run, 2 = all but one block
  Run take(std::vector<Run>&F,int mode){
    Run&top=F.back(); Run mv;
    if(mode==1 || (mode==0&&top.n==1)){ mv=top; F.pop_back(); if(mode==0&&mv.var>=0){ fail="variable run consumed"; } return mv; }
    if(mode==0){ mv={top.w,1,-1,0}; top.n-=1; if(top.var>=0){ top.off-=1; note(top);} return mv; }
    // mode 2, top.n >= 2
    mv={top.w,top.n-1,top.var,top.off-1}; if(mv.var<0) mv.off=0; note(mv);
    top.n=1; top.var=-1; top.off=0; return mv;
  }
  void push(std::vector<Run>&O,Run r){
    if(O.empty()&&r.w==0){ if(r.var>=0) fail="variable run lost in the blank"; return; }
    if(!O.empty()&&O.back().w==r.w){ Run&t=O.back();
      if(t.var>=0&&r.var>=0){ fail="two variable runs merged"; t.n+=r.n; t.var=-1; t.off=0; return; }
      if(t.var>=0){ t.n+=r.n; t.off+=r.n; note(t); }
      else if(r.var>=0){ i64 c=t.n; t.n+=r.n; t.var=r.var; t.off=r.off+c; note(t); }
      else t.n+=r.n;
      return; }
    O.push_back(r); note(r);
  }
  bool leftEmptyAfter()const{ return dir? L.empty() : (L.empty()||(L.size()==1&&L[0].n==1)); }

  // ---- node test helpers (cells from position pos of the current block c[], then the right stack) ----
  int cellAt(const int*c,int pos,i64 k)const{
    if(pos+k<2*K) return c[pos+k];
    i64 b=(pos+k-2*K)/K; int i=(int)((pos+k-2*K)%K);
    for(size_t u=R.size();u-->0;){ if(b<R[u].n) return (int)((R[u].w>>(K-1-i))&1); b-=R[u].n; }
    return 0;
  }
  void parseNode(const int*c,int pos,i64&B,std::string&T)const{
    // units: the rest of the current block (after the 8 prefix cells are skipped below), then the runs of R
    struct U{ std::string w; i64 n; };
    std::vector<U> us; { std::string s; for(int i=pos;i<2*K;i++) s+=(char)('0'+c[i]); us.push_back({s,1}); }
    for(size_t u=R.size();u-->0;){ std::string s; for(int i=0;i<K;i++) s+=(char)('0'+((R[u].w>>(K-1-i))&1)); us.push_back({s,R[u].n}); }
    size_t u=0; i64 j=0; size_t i=0;
    auto norm=[&](){ while(u<us.size()&&i>=us[u].w.size()){ i=0; j++; if(j>=us[u].n){ j=0; u++; } } };
    auto peek=[&]()->int{ norm(); return u<us.size()? us[u].w[i]-'0' : 0; };
    auto adv=[&](){ norm(); if(u<us.size()) i++; };
    norm();
    for(int q=0;q<8;q++) adv();
    std::string w01,w10; for(int q=0;q<K/2;q++){ w01+="01"; w10+="10"; }
    B=0;
    for(;;){
      norm(); if(u>=us.size()) break;
      if((int)us[u].w.size()==K && K%2==0){
        if(i==0 && us[u].w==w01){ i64 r=us[u].n-j; B+=(i64)(K/2)*r; j=0; u++; continue; }      // r whole blocks 0101..01
        if(i==1 && us[u].w==w10 && us[u].n-j>=2){ i64 r=us[u].n-j-1; B+=(i64)(K/2)*r; j+=r; continue; } // r blocks, shifted by one cell
      }
      size_t su=u; i64 sj=j; size_t si=i;
      int a=peek(); adv(); int b=peek(); adv();
      if(a==0&&b==1){ B++; continue; }
      u=su; j=sj; i=si; break;
    }
    // the tail: everything that remains, up to the last 1
    norm(); T.clear(); i128 remaining=0; for(size_t q=u;q<us.size();q++) remaining+=us[q].n-(q==u?j:0);
    if(remaining>200000){ T="HUGE"; return; }
    while(true){ norm(); if(u>=us.size()) break; T+=(char)('0'+peek()); adv(); }
    while(!T.empty()&&T.back()=='0') T.pop_back();
    if(T.empty()) T="-";
  }

  // ---- one operation ----
  void op(){
    ops++;
    std::vector<Run>&F=dir?R:L; std::vector<Run>&O=dir?L:R;   // F in front of the head, O behind the back block
    bool virgin=F.empty();
    if(leftEmptyAfter()){
      // cell by cell on one window, with the node test
      Run cur; if(virgin) cur={0,1,-1,0}; else cur=take(F,0);
      int c[64]; fill(c,dir,back,cur.w);
      int pos=dir?K:K-1, s=st; i64 t=0;
      while(pos>=0&&pos<2*K){
        if(s==0 && (steps+t)>0){
          bool ok=true; for(int i=0;i<pos&&ok;i++) if(c[i]) ok=false;
          static const int P[8]={0,1,0,0,1,0,0,0};
          for(int q=0;q<8&&ok;q++) if(cellAt(c,pos,q)!=P[q]) ok=false;
          if(ok){
            if(track){ fail="node test prefix met inside a period"; }
            else{ i64 B; std::string T; parseNode(c,pos,B,T);
              out.push_back("NODE "+s128(steps+t)+" "+std::to_string(B)+" "+T);
              if(B>=MINB){ status=NODE; steps+=t; return; } }
          }
        }
        int b=c[pos]; if(NX[s][b]<0){ steps+=t; status=HALT; return; }
        c[pos]=W[s][b]; pos+=M[s][b]; s=NX[s][b]; t++;
        if(t>INLIMIT){ status=LIMIT; info="step limit inside one window"; return; }
      }
      int xdir=pos>=2*K?1:0; u64 nb,nw; unfill(c,dir,nb,nw);
      if(virgin && xdir==dir && s==st && nw==back){ status=INF; info="runs away over the blank"; return; }
      steps+=t; if(track) s0+=t;
      st=s;
      if(xdir==dir){ push(O,Run{nb,1,-1,0}); back=nw; }
      else { push(F,Run{nw,1,-1,0}); back=nb; dir=xdir; }
      return;
    }
    u64 w=virgin?0:F.back().w;
    const Rule&r=rule(st,dir,back,w);
    if(r.halt==1){ steps+=r.t; status=HALT; return; }
    if(r.halt==2){ status=LIMIT; info="step limit inside one window"; return; }
    if(r.xdir==dir && r.st==st && r.nw==back){
      if(virgin){ status=INF; info="runs away over the blank"; return; }
      // chain step.  Leftwards on the bottom run of the left stack: leave one block (it is then handled cell by
      // cell above).  Here F.back().n >= 2 in that case, because leftEmptyAfter() is false.
      Run mv=take(F,(dir==0&&F.size()==1)?2:1);
      addSteps(r.t,mv); mv.w=r.nb; push(O,mv);
      return;
    }
    Run mv; if(virgin) mv={0,1,-1,0}; else mv=take(F,0);
    addSteps(r.t,mv); st=r.st;
    if(r.xdir==dir){ mv.w=r.nb; push(O,mv); back=r.nw; }
    else { mv.w=r.nw; push(F,mv); back=r.nb; dir=r.xdir; }
  }

  std::vector<i64> shape()const{
    std::vector<i64> v; v.push_back(st); v.push_back(dir); v.push_back((i64)back); v.push_back((i64)L.size()); v.push_back((i64)R.size());
    for(const Run&r:L){ v.push_back((i64)r.w); v.push_back(r.n<BIG?r.n:-1); }
    for(const Run&r:R){ v.push_back((i64)r.w); v.push_back(r.n<BIG?r.n:-1); }
    return v;
  }

  // returns true if a jump was made (or the run was decided)
  bool tryJump(const Snap&sn){
    Eng e; e.L=sn.L; e.R=sn.R; e.back=sn.back; e.st=sn.st; e.dir=sn.dir; e.steps=sn.steps; e.ops=sn.ops; e.track=true;
    int nv=0; std::vector<std::pair<int,size_t>> where;
    for(size_t i=0;i<e.L.size();i++) if(e.L[i].n>=BIG){ e.L[i].var=nv++; e.L[i].off=0; where.push_back({0,i}); }
    for(size_t i=0;i<e.R.size();i++) if(e.R[i].n>=BIG){ e.R[i].var=nv++; e.R[i].off=0; where.push_back({1,i}); }
    if(nv==0){ status=INF; info="exact repetition of a configuration"; return true; }
    e.minoff.assign(nv,0); e.sv.assign(nv,0); e.s0=0;
    while(e.ops<ops && e.status==RUN && !e.fail) e.op();
    if(e.fail||e.status!=RUN) return false;
    // end shape = start shape with n_v + d_v ?
    if(e.st!=sn.st||e.dir!=sn.dir||e.back!=sn.back||e.L.size()!=sn.L.size()||e.R.size()!=sn.R.size()) return false;
    std::vector<i64> d(nv,0);
    for(int side=0;side<2;side++){ const std::vector<Run>&a=side?e.R:e.L; const std::vector<Run>&b=side?sn.R:sn.L;
      for(size_t i=0;i<a.size();i++){ if(a[i].w!=b[i].w) return false;
        if(b[i].n>=BIG){ int v=-1; for(int q=0;q<nv;q++) if(where[q].first==side&&where[q].second==i) v=q;
          if(a[i].var!=v) return false;
          d[v]=a[i].off; }
        else { if(a[i].var>=0||a[i].n!=b[i].n) return false; } } }
    // the re-simulation must have reproduced the real run exactly
    if(e.st!=st||e.dir!=dir||e.back!=back||e.steps!=steps||e.ops!=ops||e.L.size()!=L.size()||e.R.size()!=R.size()) die("re-simulation differs from the run (header)");
    for(size_t i=0;i<L.size();i++) if(e.L[i].w!=L[i].w||e.L[i].n!=L[i].n) die("re-simulation differs from the run (L)");
    for(size_t i=0;i<R.size();i++) if(e.R[i].w!=R[i].w||e.R[i].n!=R[i].n) die("re-simulation differs from the run (R)");
    { i128 s=e.s0; for(int v=0;v<nv;v++){ const Run&r=(where[v].first?sn.R:sn.L)[where[v].second]; s+=e.sv[v]*r.n; }
      if(s!=steps-sn.steps) die("step polynomial differs from the run"); }
    // number of applications from the current configuration
    i128 N=-1; bool shrink=false;
    for(int v=0;v<nv;v++){ const Run&r=(where[v].first?R:L)[where[v].second]; i64 base=2-e.minoff[v];
      if(r.n<base) return false;
      if(d[v]<0){ i128 q=(i128)(r.n-base)/(-d[v])+1; if(!shrink||q<N) N=q; shrink=true; } }
    if(!shrink){ status=INF; info="proven cycle with no shrinking count"; return true; }
    if(N<=0) return false;
    i128 s=e.s0, tri=0;
    for(int v=0;v<nv;v++){ Run&r=(where[v].first?R:L)[where[v].second]; s+=e.sv[v]*r.n; tri+=e.sv[v]*d[v]; }
    steps+=N*s+tri*(N*(N-1)/2);
    for(int v=0;v<nv;v++){ Run&r=(where[v].first?R:L)[where[v].second]; r.n+=(i64)(N*d[v]); if(r.n<2) die("count below 2 after a jump"); }
    jumps++; reps+=N;
    return true;
  }

  void run(){
    std::map<std::vector<i64>,Snap> seen;
    while(status==RUN){
      if(!NOJUMP && dir==0 && leftEmptyAfter()){
        std::vector<i64> sh=shape();
        auto it=seen.find(sh);
        if(it!=seen.end()){ if(tryJump(it->second)){ seen.clear(); if(status!=RUN) break; } }
        if(seen.size()>20000) seen.clear();
        Snap sn; sn.L=L; sn.R=R; sn.back=back; sn.st=st; sn.dir=dir; sn.steps=steps; sn.ops=ops; seen[sh]=sn;
      }
      op();
      if(ops>MAXOPS&&status==RUN){ status=LIMIT; }
    }
  }
};

int main(int argc,char**argv){
  int a=1;
  for(;a<argc&&argv[a][0]=='-';a++){
    if(!strcmp(argv[a],"-K")) K=atoi(argv[++a]);
    else if(!strcmp(argv[a],"-big")) BIG=atoll(argv[++a]);
    else if(!strcmp(argv[a],"-minB")) MINB=atoll(argv[++a]);
    else if(!strcmp(argv[a],"-maxops")) MAXOPS=atoll(argv[++a]);
    else if(!strcmp(argv[a],"-nojump")) NOJUMP=true;
    else die("unknown option");
  }
  if(a>=argc) die("machine missing");
  if(K<2||K>24||K%2) die("K must be even, 2..24");
  if(BIG<4) die("big must be >= 4");
  const char*spec=argv[a];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*p=spec+s*7+b*3; if(p[0]=='-'){NX[s][b]=-1;W[s][b]=0;M[s][b]=1;}else{W[s][b]=p[0]-'0';M[s][b]=p[1]=='R'?1:-1;NX[s][b]=p[2]-'A';}}
  std::string line;
  while(std::getline(std::cin,line)){
    if(line.empty()) continue;
    Eng e;
    if(line!="blank"){
      std::istringstream is(line); i64 B; std::string T; is>>B>>T; if(T=="-") T="";
      // cells: 01001000 (01)^B T, cut into K-cell blocks from the head cell on
      std::string head="01001000"; i64 j=0; while(j<B && (head.size()%K!=0)){ head+="01"; j++; }
      i64 q=0, rem=B-j; std::string rest;
      if(head.size()%K==0){ q=rem/(K/2); rem-=q*(K/2); }
      else rest=head, head="";                       // B too small to reach a block boundary: all literal
      for(i64 i=0;i<rem;i++) rest+="01";
      rest+=T; while(rest.size()%K) rest+="0";
      std::vector<Run> blocks;   // left to right
      auto addw=[&](const std::string&s){ for(size_t i=0;i<s.size();i+=K){ u64 w=0; for(int k=0;k<K;k++) w=(w<<1)|(u64)(s[i+k]-'0');
          if(!blocks.empty()&&blocks.back().w==w) blocks.back().n++; else blocks.push_back({w,1,-1,0}); } };
      addw(head);
      if(q>0){ u64 w=0; for(int k=0;k<K;k++) w=(w<<1)|(u64)(k&1); if(!blocks.empty()&&blocks.back().w==w) blocks.back().n+=q; else blocks.push_back({w,q,-1,0}); }
      addw(rest);
      while(!blocks.empty()&&blocks.back().w==0) blocks.pop_back();
      for(size_t i=blocks.size();i-->0;) e.R.push_back(blocks[i]);
    }
    e.run();
    for(auto&s:e.out) printf("%s\n",s.c_str());
    if(e.status==HALT) printf("HALT %s\n",s128(e.steps).c_str());
    else if(e.status==INF) printf("INF %s\n",e.info.c_str());
    else if(e.status==LIMIT) printf("LIMIT\n");
    printf("# ops=%lld jumps=%lld reps=%s\n",e.ops,e.jumps,s128(e.reps).c_str());
    fflush(stdout);
  }
  return 0;
}
