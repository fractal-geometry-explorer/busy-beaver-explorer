// learncls: learn classes of half tapes that predict the return state of every trip of the real run, then run
// the call-summary decider on them.
// A class is a row of an observation table: the outcomes of a list of experiments (w, s) -- put the cells w in
// front of the half tape, enter in state s -- on a representative tape (return state, 6 = halt, 7 = no return
// within CAP steps). phi(c, q) = class of c . representative(q), so the class of a tape is a fold from its far
// end. The real run is the teacher: when a trip returns in a state its class did not predict, the tail is cut
// at the first place where replacing its far part by the representative changes the outcome, and the near part
// becomes a new experiment (Rivest and Schapire's counterexample rule).
// Usage: LEARN=<steps> learncls MACHINE L|R 0 100 SEEDSTEPS CAP MAXCLS
//   (with LEARN unset and a first number K > 0 it is the older variant: experiments are the frequent K-cell call keys)
#include <bits/stdc++.h>
using namespace std;
typedef vector<uint8_t> Tape;
static int W[6][2],D[6][2],NX[6][2];
static long CAP=20000; static int RESK=0;
struct Exp { Tape w; int s; };
static vector<Exp> E;
// simulate on half tape t (index 0 = nearest cell), entering cell 0 in state s. Returns outcome 0..5 = return state, 6 = halt, 7 = timeout.
static int sim(Tape &t,int s){ long p=0; for(long i=0;i<CAP;i++){ if(p>=(long)t.size()) t.resize(p+1,0); int b=t[p]; if(NX[s][b]<0) return 6; t[p]=W[s][b]; int d=D[s][b]; s=NX[s][b]; p+=d; if(p<0) return s; } return 7; }
static void trim(Tape&t){ while(!t.empty()&&t.back()==0) t.pop_back(); }
struct Cls { Tape rep; string row; };
static vector<Cls> cls; static unordered_map<string,int> rowmap; static long nsim=0;
static int classify(const Tape&x){
  string row; row.reserve(E.size()*(1+RESK));
  Tape t;
  for(auto&e:E){ t.assign(e.w.begin(),e.w.end()); t.insert(t.end(),x.begin(),x.end()); int o=sim(t,e.s); nsim++; row.push_back((char)('0'+o));
    for(int j=0;j<RESK;j++) row.push_back(o<6 && j<(int)t.size()? (char)('a'+t[j]) : (o<6?'a':'x')); }
  auto it=rowmap.find(row); if(it!=rowmap.end()) return it->second;
  int id=cls.size(); cls.push_back({x,row}); rowmap[row]=id; return id;
}
static unordered_map<long,int> phimemo; static vector<vector<pair<int,int>>> U; // U[q] = (c, qi)
struct Key { int s,q; bool operator==(const Key&o)const{return s==o.s&&q==o.q;} };
struct KH { size_t operator()(const Key&k)const{ return (size_t)k.q*7+k.s; } };
static unordered_map<Key,set<pair<int,int>>,KH> Sum; static unordered_map<Key,set<long>,KH> deps; // dependents: encoded contract ids, -1 = top
static unordered_map<int,set<long>> udeps; // contracts that unfolded class q
static deque<long> work; static unordered_set<long> inwork; static unordered_set<long> known;
static inline long enc(int s,int q){ return (long)q*6+s; }
static void push(long c){ if(inwork.insert(c).second) work.push_back(c); }
static int phi(int c,int q){ long k=(long)q*2+c; auto it=phimemo.find(k); if(it!=phimemo.end()) return it->second;
  Tape t; t.push_back(c); t.insert(t.end(),cls[q].rep.begin(),cls[q].rep.end()); trim(t);
  int r=classify(t); phimemo[k]=r; if((int)U.size()<=r) U.resize(r+1); U[r].push_back({c,q});
  for(long d:udeps[r]) push(d);
  return r; }
static bool halted=false; static string haltinfo;
static void need(long c){ if(known.insert(c).second) push(c); }
static void evalc(long id){ int s=id%6, q=id/6; udeps[q].insert(id);
  set<tuple<int,int,int>> seen; vector<tuple<int,int,int>> st;
  if((int)U.size()<=q) U.resize(q+1);
  for(size_t i=0;i<U[q].size();i++){ auto m=make_tuple(s,U[q][i].first,U[q][i].second); if(seen.insert(m).second) st.push_back(m); }
  auto &res=Sum[{s,q}]; bool changed=false;
  while(!st.empty()){ auto [a,c1,qi]=st.back(); st.pop_back();
    if(NX[a][c1]<0){ halted=true; haltinfo="contract s="+string(1,'A'+s)+" q="+to_string(q)+" micro "+string(1,'A'+a)+to_string(c1); return; }
    int w=W[a][c1], d=D[a][c1], a2=NX[a][c1];
    if(d<0){ int r=phi(w,qi); if(res.insert({a2,r}).second) changed=true; }
    else { long cc=enc(a2,qi); need(cc); deps[{a2,qi}].insert(id);
      auto it=Sum.find({a2,qi}); if(it!=Sum.end()) { vector<pair<int,int>> tmp(it->second.begin(),it->second.end()); for(auto&pr:tmp){ auto m=make_tuple(pr.first,w,pr.second); if(seen.insert(m).second) st.push_back(m); } } }
  }
  if(changed) for(long d_:deps[{s,q}]) push(d_);
}
static set<tuple<int,int,int>> top;
static void evaltop(){ vector<tuple<int,int,int>> st(top.begin(),top.end());
  while(!st.empty()){ auto [a,c,q]=st.back(); st.pop_back();
    if(NX[a][c]<0){ halted=true; haltinfo="top "+string(1,'A'+a)+to_string(c)+" q="+to_string(q); return; }
    int w=W[a][c], d=D[a][c], a2=NX[a][c];
    if(d<0){ auto n=make_tuple(a2,0,phi(w,q)); if(top.insert(n).second) st.push_back(n); }
    else { need(enc(a2,q)); deps[{a2,q}].insert(-1);
      auto it=Sum.find({a2,q}); if(it!=Sum.end()){ vector<pair<int,int>> tmp(it->second.begin(),it->second.end()); for(auto&pr:tmp){ auto n=make_tuple(pr.first,w,pr.second); if(top.insert(n).second) st.push_back(n); } } }
  }
}

static int einIdx[6]; // index of experiment (empty, s)
static int addExperiment(const Exp&e){ // extend all rows by one column; classes can only split
  E.push_back(e); Tape t; rowmap.clear();
  size_t n0=cls.size();
  vector<string> oldrow(n0);
  for(size_t q=0;q<n0;q++){ oldrow[q]=cls[q].row; t.assign(e.w.begin(),e.w.end()); t.insert(t.end(),cls[q].rep.begin(),cls[q].rep.end()); int o=sim(t,e.s); nsim++; cls[q].row.push_back((char)('0'+o)); rowmap[cls[q].row]=q; }
  vector<pair<long,int>> ents(phimemo.begin(),phimemo.end());
  for(auto&kv:ents){ int c=kv.first%2; int q=kv.first/2; int r=kv.second; if((size_t)q>=n0||(size_t)r>=n0) continue;
    Tape x; x.push_back(c); x.insert(x.end(),cls[q].rep.begin(),cls[q].rep.end()); trim(x);
    t.assign(e.w.begin(),e.w.end()); t.insert(t.end(),x.begin(),x.end()); int o=sim(t,e.s); nsim++;
    string nr=oldrow[r]; nr.push_back((char)('0'+o));
    if(nr==cls[r].row) continue;
    auto it=rowmap.find(nr); int id; if(it!=rowmap.end()) id=it->second; else { id=cls.size(); cls.push_back({x,nr}); rowmap[nr]=id; }
    phimemo[kv.first]=id; }
  U.assign(cls.size(),{}); for(auto&kv:phimemo) U[kv.second].push_back({(int)(kv.first%2),(int)(kv.first/2)});
  return 0; }
// one pass of the real run with the fold classes maintained online; returns true if a counterexample was found and used
static bool learnPass(long NS,int q0,long &cexStep){
  long T=1L<<25; static vector<uint8_t> tape; tape.assign(T,0); static vector<int> C; C.assign(T,q0);
  struct Fr{ long b; int s; int cl; long t0; }; vector<Fr> st; long p=T/2; int s=0; long hi=p;
  long bad_t0=-1, bad_b=-1; int bad_s=-1;
  for(long i=0;i<NS;i++){ int b=tape[p]; if(NX[s][b]<0) break; tape[p]=W[s][b]; int d=D[s][b]; s=NX[s][b]; long op=p; p+=d; if(p>hi)hi=p;
    if(d>0){ st.push_back({op,s,C[op],i}); }
    else { C[op-1]=phi(tape[op],C[op]);
      if(!st.empty()){ Fr f=st.back(); st.pop_back(); int pred=cls[f.cl].row[einIdx[f.s]]-'0';
        if(pred!=s && i-f.t0<CAP/2){ bad_t0=f.t0; bad_b=f.b; bad_s=f.s; break; } } }
  }
  if(bad_t0<0) return false;
  // rerun to the start of the bad trip and take the tail
  tape.assign(T,0); p=T/2; s=0; hi=p;
  for(long i=0;i<=bad_t0;i++){ int b=tape[p]; tape[p]=W[s][b]; int d=D[s][b]; s=NX[s][b]; p+=d; if(p>hi)hi=p; }
  Tape t(tape.begin()+bad_b+1, tape.begin()+hi+2); trim(t); int n=t.size();
  vector<int> f(n+1); f[n]=q0; for(int i=n-1;i>=0;i--) f[i]=phi(t[i],f[i+1]);
  int prev=-1; Tape x;
  for(int i=0;i<=n;i++){ x.assign(t.begin(),t.begin()+i); x.insert(x.end(),cls[f[i]].rep.begin(),cls[f[i]].rep.end()); int o=sim(x,bad_s); nsim++;
    if(i>0 && o!=prev){ Exp e; e.w.assign(t.begin(),t.begin()+(i-1)); e.s=bad_s; addExperiment(e); cexStep=bad_t0; return true; }
    prev=o; }
  cexStep=-bad_t0; return true; // no change point found within CAP (should not happen)
}

static void obsPass(long NS,int q0){
  long T=1L<<25; static vector<uint8_t> tape; tape.assign(T,0); static vector<int> C; C.assign(T,q0);
  struct Fr{ long b; int s; int cl; long t0; }; vector<Fr> st; long p=T/2; int s=0;
  map<pair<int,int>,map<int,long>> ob; set<int> used; long ntr=0;
  for(long i=0;i<NS;i++){ int b=tape[p]; if(NX[s][b]<0) break; tape[p]=W[s][b]; int d=D[s][b]; s=NX[s][b]; long op=p; p+=d;
    if(d>0){ st.push_back({op,s,C[op],i}); }
    else { C[op-1]=phi(tape[op],C[op]); used.insert(C[op-1]);
      if(!st.empty()){ Fr f=st.back(); st.pop_back(); ob[{f.cl,f.s}][C[op-1]*6+s]++; ntr++; } } }
  long multi=0, mtr=0; size_t facts=0; for(auto&kv:ob){ facts+=kv.second.size(); if(kv.second.size()>1){ multi++; for(auto&x:kv.second) mtr+=x.second; } }
  fprintf(stderr,"real run: classes used=%zu contracts=%zu facts=%zu multi-valued contracts=%ld (%.3f of %ld trips)\n",used.size(),ob.size(),facts,multi,(double)mtr/ntr,ntr);
}
int main(int argc,char**argv){
  char*m=argv[1]; bool mirror=argv[2][0]=='R'; int KE=atoi(argv[3]); long minc=atol(argv[4]); long NS=atol(argv[5]); if(argc>6) CAP=atol(argv[6]); long MAXC= argc>7? atol(argv[7]):200000; if(argc>8) RESK=atoi(argv[8]);
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*x=m+7*s+3*b; if(x[0]=='-'){NX[s][b]=-1;continue;} W[s][b]=x[0]-'0'; D[s][b]=x[1]=='R'?1:-1; if(mirror)D[s][b]=-D[s][b]; NX[s][b]=x[2]-'A';}
  // seed run: count call keys (state, KE cells right of the boundary) over all rightward trips
  { long T=1L<<26; vector<uint8_t> tape(T,0); long p=T/2; int s=0; unordered_map<uint64_t,long> cnt; int sin=0;
    for(long i=0;i<NS;i++){ int b=tape[p]; if(NX[s][b]<0){ printf("%s HALT in seed run\n",m); return 0; } tape[p]=W[s][b]; int d=D[s][b]; s=NX[s][b]; p+=d;
      if(d>0){ sin|=1<<s; uint64_t k=0; for(int j=0;j<KE;j++) k|=(uint64_t)tape[p+j]<<j; cnt[k*8+s]++; } }
    for(int s2=0;s2<6;s2++) if(sin>>s2&1) E.push_back({Tape(),s2});
    vector<pair<long,uint64_t>> v; for(auto&kv:cnt) if(kv.second>=minc) v.push_back({kv.second,kv.first}); sort(v.rbegin(),v.rend());
    for(auto&pr:v){ Exp e; e.s=pr.second%8; uint64_t k=pr.second/8; for(int j=0;j<KE;j++) e.w.push_back(k>>j&1); E.push_back(e); }
    if(KE==0) E.resize(__builtin_popcount(sin));
  }
  fprintf(stderr,"experiments: %zu\n",E.size());
  int q0=classify(Tape()); U.resize(1); phimemo[(long)q0*2+0]=q0; U[q0].push_back({0,q0});
  for(int z=0;z<6;z++) einIdx[z]=-1; for(size_t i=0;i<E.size();i++) if(E[i].w.empty()) einIdx[E[i].s]=i;
  long LS= getenv("LEARN")? atol(getenv("LEARN")):0; int rounds=0; long last=0;
  if(LS>0){ for(;rounds<100000;rounds++){ long cs=0; if(!learnPass(LS,q0,cs)) break; last=cs; if(cs<0){ fprintf(stderr,"no change point at %ld\n",-cs); break; }
      if(rounds%50==0) fprintf(stderr,"round %d: cex at step %ld, exps=%zu classes=%zu maxw=%zu\n",rounds,cs,E.size(),cls.size(),E.back().w.size()); if((long)cls.size()>MAXC) break; }
    size_t mw=0; for(auto&e:E) mw=max(mw,e.w.size());
    fprintf(stderr,"learned: rounds=%d exps=%zu classes=%zu longest w=%zu last cex step=%ld\n",rounds,E.size(),cls.size(),mw,last); }
  if(LS>0) obsPass(LS,q0);
  top.insert(make_tuple(0,0,q0)); push(-1);
  long it=0;
  while(!work.empty()){ long c=work.front(); work.pop_front(); inwork.erase(c); it++;
    if(c==-1) evaltop(); else evalc(c);
    if(halted) break; if((long)cls.size()>MAXC) break; }
  size_t nsum=0; for(auto&kv:Sum) nsum+=kv.second.size();
  printf("%s %c KE=%d exps=%zu : %s  classes=%zu contracts=%zu summaries=%zu top=%zu sims=%ld %s\n",m,argv[2][0],KE,E.size(), halted?"HALT-REACHABLE": ((long)cls.size()>MAXC?"LIMIT":"NONHALT"), cls.size(),known.size(),nsum,top.size(),nsim,haltinfo.c_str());
  return 0;
}
