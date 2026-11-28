// lsum_cegar: call-summary decider with classes of half tapes learned by counterexamples. EXPERIMENTAL: on both
// machines of cryptids pull request 42 the refinement splits classes without end (see followup/write-only-test.md).
// The abstraction only unfolds a class into (cell, class) pairs seen in the real run; a derivation that leaves
// them counts like a halt and is refined or, if nothing separates the tapes, allowed.
//
// Half tape = the cells right of a boundary, head not inside. A class is a row of an observation table: the
// outcomes of a list of experiments on a representative tape. An experiment is a list of steps (w, s): put the
// cells w in front, enter in state s, wait for the return. phi(c, q) = class of c . rep(q), so the class of a tape
// is a fold from its far end (an automaton reading the tape from the far end).
//
// The decider computes, for the classes it needs, summaries (s, q) -> {(s', q')} or HALT as a least fixed point
// (each fact keeps one derivation), with the left frontier as top level. If HALT is not derivable the machine
// does not halt. Otherwise the derivation is replayed on concrete tapes; where the replay leaves the derivation,
// two concrete tapes of one class behave differently and a new experiment separates them (Rivest-Schapire).
//
// Usage: lsum_cegar MACHINE L|R [LEARNSTEPS=1000000] [CAP=200000] [MAXROUNDS=5000] [MAXCLS=50000]
#include <bits/stdc++.h>
using namespace std;
typedef vector<uint8_t> Tape;
static int W[6][2],D[6][2],NX[6][2];
static long CAP=200000;
static long nsim=0;
static int sim(Tape &t,int s,long cap=-1){ if(cap<0)cap=CAP; nsim++; long p=0; for(long i=0;i<cap;i++){ if(p>=(long)t.size()) t.resize(p+1,0); int b=t[p]; if(NX[s][b]<0) return 6; t[p]=W[s][b]; int d=D[s][b]; s=NX[s][b]; p+=d; if(p<0) return s; } return 7; }
static void trim(Tape&t){ while(!t.empty()&&t.back()==0) t.pop_back(); }
struct Exp { vector<pair<Tape,int>> st; };
static vector<Exp> E; static int einIdx[6];
static int simExp(const Exp&e,const Tape&x){ Tape t=x; int o=7; for(auto&pr:e.st){ Tape u(pr.first); u.insert(u.end(),t.begin(),t.end()); o=sim(u,pr.second); if(o>=6) return o; t.swap(u); } return o; }
struct Cls { Tape rep; string row; };
static vector<Cls> cls; static unordered_map<string,int> rowmap;
static unordered_map<long,int> phimemo; static vector<vector<pair<int,int>>> U;
static string rowOf(const Tape&x){ string r; for(auto&e:E) r.push_back((char)('0'+simExp(e,x))); return r; }
static int classOfRow(const string&row,const Tape&x){ auto it=rowmap.find(row); if(it!=rowmap.end()) return it->second; int id=cls.size(); cls.push_back({x,row}); rowmap[row]=id; if((int)U.size()<=id) U.resize(id+1); return id; }
static bool phiNew=false;
static int phi(int c,int q){ long k=(long)q*2+c; auto it=phimemo.find(k); if(it!=phimemo.end()) return it->second;
  Tape t; t.push_back(c); t.insert(t.end(),cls[q].rep.begin(),cls[q].rep.end()); trim(t);
  int r=classOfRow(rowOf(t),t); phimemo[k]=r; if((int)U.size()<=r) U.resize(r+1); U[r].push_back({c,q}); phiNew=true; return r; }
static vector<int> foldAll(const Tape&t){ int n=t.size(); vector<int> f(n+1); f[n]=0; for(int i=n-1;i>=0;i--) f[i]=phi(t[i],f[i+1]); return f; }
static int foldOf(Tape t){ trim(t); return foldAll(t)[0]; }
static void addExperiment(const Exp&e){ E.push_back(e); rowmap.clear(); size_t n0=cls.size(); vector<string> oldrow(n0);
  for(size_t q=0;q<n0;q++){ oldrow[q]=cls[q].row; cls[q].row.push_back((char)('0'+simExp(e,cls[q].rep))); rowmap[cls[q].row]=q; }
  vector<pair<long,int>> ents(phimemo.begin(),phimemo.end()); sort(ents.begin(),ents.end());
  for(auto&kv:ents){ int c=kv.first%2; int q=kv.first/2; int r=kv.second;
    Tape x; x.push_back(c); x.insert(x.end(),cls[q].rep.begin(),cls[q].rep.end()); trim(x);
    string nr=oldrow[r]; nr.push_back((char)('0'+simExp(e,x)));
    if(nr==cls[r].row) continue;
    phimemo[kv.first]=classOfRow(nr,x); if(cls.size()>oldrow.size()) oldrow.push_back(nr.substr(0,nr.size()-1)); }
  U.assign(cls.size(),{}); for(auto&kv:phimemo) U[kv.second].push_back({(int)(kv.first%2),(int)(kv.first/2)}); }
// Rivest-Schapire: tape t mispredicts experiment e (outcome on t differs from the row of its class). Adds one experiment.
static bool RS(Tape t,const Exp&e){ trim(t); int n=t.size(); vector<int> f=foldAll(t); int prev=-1; Tape x;
  for(int i=0;i<=n;i++){ x.assign(t.begin(),t.begin()+i); x.insert(x.end(),cls[f[i]].rep.begin(),cls[f[i]].rep.end()); int o=simExp(e,x);
    if(i>0 && o!=prev){ Exp e2=e; e2.st[0].first.insert(e2.st[0].first.end(),t.begin(),t.begin()+(i-1)); addExperiment(e2); return true; }
    prev=o; }
  return false; }
static Exp expIn(int s){ Exp e; e.st.push_back({Tape(),s}); return e; }
// ---------- learning from the real run: return states of all trips must be predicted ----------
static bool learnPass(long NS){
  long T=1L<<25; static vector<uint8_t> tape; tape.assign(T,0); static vector<int> C; C.assign(T,0);
  struct Fr{ long b; int s; int cl; long t0; }; vector<Fr> st; long p=T/2; int s=0; long hi=p; long bad_t0=-1,bad_b=-1; int bad_s=-1;
  for(long i=0;i<NS;i++){ int b=tape[p]; if(NX[s][b]<0) break; tape[p]=W[s][b]; int d=D[s][b]; s=NX[s][b]; long op=p; p+=d; if(p>hi)hi=p;
    if(d>0) st.push_back({op,s,C[op],i});
    else { C[op-1]=phi(tape[op],C[op]);
      if(!st.empty()){ Fr f=st.back(); st.pop_back(); int pred=cls[f.cl].row[einIdx[f.s]]-'0'; if(pred!=s && i-f.t0<CAP/2){ bad_t0=f.t0; bad_b=f.b; bad_s=f.s; break; } } } }
  if(bad_t0<0) return false;
  tape.assign(T,0); p=T/2; s=0; hi=p;
  for(long i=0;i<=bad_t0;i++){ int b=tape[p]; tape[p]=W[s][b]; int d=D[s][b]; s=NX[s][b]; p+=d; if(p>hi)hi=p; }
  Tape t(tape.begin()+bad_b+1, tape.begin()+hi+2);
  if(!RS(t,expIn(bad_s))){ fprintf(stderr,"learnPass: no change point\n"); return false; }
  return true; }
// ---------- what the real run shows, with the current classes ----------
static long LSTEPS=1000000;
static set<long> obsPhi, allowPhi; static vector<vector<pair<int,int>>> Uobs;
static map<int,pair<long,long>> exCls; static map<pair<long,pair<int,int>>,pair<long,long>> exFact; // examples: (time, boundary)
static Tape retrieve(long t,long bnd){ long T=1L<<25; static vector<uint8_t> tape; tape.assign(T,0); long p=T/2; int s=0; long hi=p;
  for(long i=0;i<=t;i++){ int b=tape[p]; tape[p]=W[s][b]; int d=D[s][b]; s=NX[s][b]; p+=d; if(p>hi)hi=p; }
  Tape x(tape.begin()+bnd+1,tape.begin()+hi+2); trim(x); return x; }
static void obsPass(long NS){ obsPhi.clear(); exCls.clear(); exFact.clear();
  long T=1L<<25; static vector<uint8_t> tape; tape.assign(T,0); static vector<int> C; C.assign(T,0);
  struct Fr{ long b; int s; int cl; long t0; }; vector<Fr> st; long p=T/2; int s=0;
  obsPhi.insert(0);
  for(long i=0;i<NS;i++){ int b=tape[p]; if(NX[s][b]<0) break; tape[p]=W[s][b]; int d=D[s][b]; s=NX[s][b]; long op=p; p+=d;
    if(d>0) st.push_back({op,s,C[op],i});
    else { int r=phi(tape[op],C[op]); obsPhi.insert((long)C[op]*2+tape[op]); C[op-1]=r; if(!exCls.count(r)) exCls[r]={i,op-1};
      if(!st.empty()){ Fr f=st.back(); st.pop_back(); if(i-f.t0<CAP/2){ auto key=make_pair((long)f.cl*6+f.s,make_pair(s,r)); if(!exFact.count(key)) exFact[key]={f.t0,f.b}; } } } }
  Uobs.assign(cls.size(),{}); for(long k:obsPhi) Uobs[phimemo[k]].push_back({(int)(k%2),(int)(k/2)});
  for(long k:allowPhi) if(!obsPhi.count(k) && phimemo.count(k)) Uobs[phimemo[k]].push_back({(int)(k%2),(int)(k/2)});
}
static inline bool okPhi(int c,int q){ long k=(long)q*2+c; return obsPhi.count(k)||allowPhi.count(k); }
// ---------- decider with derivations ----------
typedef long Fact; // contract*4096 ... we encode separately
struct Res { int s; int q; bool operator<(const Res&o)const{ return s!=o.s? s<o.s : q<o.q; } bool operator==(const Res&o)const{return s==o.s&&q==o.q;} }; // s==6: HALT
struct Prov { int c1,qi; vector<pair<long,Res>> inner; bool selfHalt; long esc; };
static map<long,map<Res,Prov>> Sum; static map<long,set<long>> deps; static map<int,set<long>> udeps;
static deque<long> work; static set<long> inwork, known;
static inline long enc(int s,int q){ return (long)q*6+s; }
static void push(long c){ if(inwork.insert(c).second) work.push_back(c); }
static void need(long c){ if(known.insert(c).second) push(c); }
struct Micro { int a,c1,qi; int parent; long ic; Res ir; };
static void evalc(long id){ int s=id%6, q=id/6; udeps[q].insert(id);
  vector<Micro> nodes; map<tuple<int,int,int>,int> seen; vector<int> st;
  if((int)Uobs.size()<=q) Uobs.resize(q+1);
  for(size_t i=0;i<Uobs[q].size();i++){ auto m=make_tuple(s,Uobs[q][i].first,Uobs[q][i].second); if(!seen.count(m)){ seen[m]=nodes.size(); nodes.push_back({s,Uobs[q][i].first,Uobs[q][i].second,-1,0,{0,0}}); st.push_back(nodes.size()-1);} }
  auto &res=Sum[id]; bool changed=false;
  auto mkprov=[&](int ix,bool selfHalt){ Prov pv; pv.selfHalt=selfHalt; pv.esc=-1; vector<pair<long,Res>> inn; int j=ix; while(nodes[j].parent>=0){ inn.push_back({nodes[j].ic,nodes[j].ir}); j=nodes[j].parent; } reverse(inn.begin(),inn.end()); pv.inner=inn; pv.c1=nodes[j].c1; pv.qi=nodes[j].qi; return pv; };
  while(!st.empty()){ int ix=st.back(); st.pop_back(); int a=nodes[ix].a,c1=nodes[ix].c1,qi=nodes[ix].qi;
    if(NX[a][c1]<0){ Res r{6,0}; if(!res.count(r)){ res[r]=mkprov(ix,true); changed=true; } continue; }
    int w=W[a][c1], d=D[a][c1], a2=NX[a][c1];
    if(d<0){ if(!okPhi(w,qi)){ Res r{6,0}; if(!res.count(r)){ res[r]=mkprov(ix,true); res[r].esc=(long)qi*2+w; changed=true; } continue; }
      Res r{a2,phi(w,qi)}; if(!res.count(r)){ res[r]=mkprov(ix,false); changed=true; } }
    else { long cc=enc(a2,qi); need(cc); deps[cc].insert(id);
      auto it=Sum.find(cc); if(it!=Sum.end()) for(auto&kv:it->second){ const Res&ir=kv.first;
        if(ir.s==6){ Res r{6,0}; if(!res.count(r)){ Prov pv=mkprov(ix,false); pv.inner.push_back({cc,ir}); res[r]=pv; changed=true; } continue; }
        auto m=make_tuple(ir.s,w,ir.q); if(!seen.count(m)){ seen[m]=nodes.size(); nodes.push_back({ir.s,w,ir.q,ix,cc,ir}); st.push_back(nodes.size()-1); } } }
  }
  if(changed) for(long d_:deps[id]) push(d_);
}
struct TopN { int a,c,q; int parent; int kind; long ic; Res ir; }; // kind 0 = start, 1 = left move, 2 = call
static vector<TopN> topn; static map<tuple<int,int,int>,int> topseen; static int haltTop=-1; static long haltIc=-1; static bool haltDirect=false; static long haltEsc=-1;
static void evaltop(){ vector<int> st; for(size_t i=0;i<topn.size();i++) st.push_back(i);
  while(!st.empty()){ int ix=st.back(); st.pop_back(); int a=topn[ix].a,c=topn[ix].c,q=topn[ix].q;
    if(NX[a][c]<0){ if(haltTop<0){ haltTop=ix; haltDirect=true; } continue; }
    int w=W[a][c], d=D[a][c], a2=NX[a][c];
    if(d<0){ if(!okPhi(w,q)){ if(haltTop<0){ haltTop=ix; haltDirect=true; haltEsc=(long)q*2+w; } continue; }
      auto n=make_tuple(a2,0,phi(w,q)); if(!topseen.count(n)){ topseen[n]=topn.size(); topn.push_back({a2,0,get<2>(n),ix,1,0,{0,0}}); st.push_back(topn.size()-1); } }
    else { long cc=enc(a2,q); need(cc); deps[cc].insert(-1);
      auto it=Sum.find(cc); if(it!=Sum.end()) for(auto&kv:it->second){ const Res&ir=kv.first;
        if(ir.s==6){ if(haltTop<0){ haltTop=ix; haltDirect=false; haltIc=cc; } continue; }
        auto n=make_tuple(ir.s,w,ir.q); if(!topseen.count(n)){ topseen[n]=topn.size(); topn.push_back({ir.s,w,ir.q,ix,2,cc,ir}); st.push_back(topn.size()-1); } } }
  } }
static void resetDecider(){ Sum.clear(); deps.clear(); udeps.clear(); work.clear(); inwork.clear(); known.clear(); topn.clear(); topseen.clear(); haltTop=-1; haltIc=-1; haltDirect=false; haltEsc=-1; }
static int runDecider(long maxcls){ resetDecider(); topn.push_back({0,0,0,-1,0,0,{0,0}}); topseen[make_tuple(0,0,0)]=0; push(-1);
  while(!work.empty()){ long c=work.front(); work.pop_front(); inwork.erase(c);
    if(c==-1) evaltop(); else evalc(c);
    if(haltTop>=0) return 1; if((long)cls.size()>maxcls) return 2; }
  return 0; }
// ---------- concretisation ----------
static string why; static bool sameClass=false; static long lastEsc=-1;
// two tapes Y, X of one class behave differently under input a; add an experiment. returns true if refined.
static bool separate(const Tape&Y,const Tape&X,int a){ int q=foldOf(Y); int pred=cls[q].row[einIdx[a]]-'0';
  Tape y=Y, x=X; int oY=sim(y,a), oX=sim(x,a);
  if(oY!=pred){ if(RS(Y,expIn(a))) return true; why="RS failed on Y"; return false; }
  if(oX!=pred){ if(RS(X,expIn(a))) return true; why="RS failed on X"; return false; }
  if(oY>=6){ why="both stop the same way"; return false; }
  trim(y); trim(x); int qY=foldOf(y), qX=foldOf(x); if(qY==qX){ why="same result class"; sameClass=true; return false; }
  int best=-1; size_t bl=1<<30; for(size_t i=0;i<E.size();i++) if(cls[qY].row[i]!=cls[qX].row[i]){ size_t l=0; for(auto&pr:E[i].st) l+=pr.first.size()+1; if(l<bl){bl=l;best=i;} }
  const Exp e=E[best]; int vY=simExp(e,y), vX=simExp(e,x);
  if(vY!=cls[qY].row[best]-'0'){ if(RS(y,e)) return true; why="RS failed on result of Y"; return false; }
  if(vX!=cls[qX].row[best]-'0'){ if(RS(x,e)) return true; why="RS failed on result of X"; return false; }
  Exp e2=expIn(a); for(auto&pr:e.st) e2.st.push_back(pr);
  int rq=simExp(e2,cls[q].rep);
  if(simExp(e2,Y)!=rq){ if(RS(Y,e2)) return true; }
  if(simExp(e2,X)!=rq){ if(RS(X,e2)) return true; }
  why="composite experiment did not separate"; return false; }
// witness of a fact: a concrete tape of the contract's class on which the derivation happens. 0 = found, 1 = refined, 2 = failed
static int witness(long cid,const Res&r,Tape&out,int depth){ if(depth>400){ why="derivation too deep"; return 2; }
  { auto it=exFact.find(make_pair(cid,make_pair(r.s,r.q))); if(r.s!=6 && it!=exFact.end()){ out=retrieve(it->second.first,it->second.second); return 0; } }
  const Prov&pv=Sum[cid][r]; int s=cid%6; Tape T; T.push_back(pv.c1); if(r.s==6 && pv.esc>=0) lastEsc=pv.esc;
  if(pv.inner.empty()){ auto it=exCls.find(pv.qi); if(it!=exCls.end()){ Tape y=retrieve(it->second.first,it->second.second); T.insert(T.end(),y.begin(),y.end()); } else T.insert(T.end(),cls[pv.qi].rep.begin(),cls[pv.qi].rep.end()); out=T; return 0; }
  Tape X1; int rc=witness(pv.inner[0].first,pv.inner[0].second,X1,depth+1); if(rc) return rc;
  T.insert(T.end(),X1.begin(),X1.end()); out=T;
  // replay with the boundary after cell 0 monitored
  Tape cur=T; int a=s; size_t j=0;
  for(;;){ int b=cur[0]; if(NX[a][b]<0){ if(r.s==6 && pv.selfHalt && j==pv.inner.size()) return 0; why="replay halts on cell"; return 2; }
    cur[0]=W[a][b]; int d=D[a][b]; a=NX[a][b];
    if(d<0){ if(j==pv.inner.size() && (r.s==a || (r.s==6 && pv.selfHalt))) return 0; why="replay returns early"; return 2; }
    if(j>=pv.inner.size()){ why="replay makes an extra call"; return 2; }
    Tape Y(cur.begin()+1,cur.end()); Tape Y2=Y; int o=sim(Y2,a); trim(Y2); const Res&fr=pv.inner[j].second;
    bool match = (fr.s==6)? (o==6) : (o==fr.s && foldOf(Y2)==fr.q);
    if(!match){ Tape X; if(j==0) X=X1; else { int rc2=witness(pv.inner[j].first,fr,X,depth+1); if(rc2) return rc2; }
      return separate(Y,X,a)? 1 : 2; }
    if(o==6) return 0;
    cur.resize(1); cur.insert(cur.end(),Y2.begin(),Y2.end()); a=o; j++; }
}
static long TOPCAP=50000000;
// replay the top-level derivation on the real machine. 0 = real halt, 1 = refined, 2 = failed
static int concretize(){ vector<int> chain; for(int ix=haltTop;ix>=0;ix=topn[ix].parent) chain.push_back(ix); reverse(chain.begin(),chain.end());
  Tape inner; int a=0; int c=0; // top-level: head on cell c, half tape 'inner' to its right, blank to the left
  for(size_t k=0;k<=chain.size();k++){ bool last=(k+1>=chain.size()+0) && false; (void)last;
    // at node chain[k] (k < size): config (a,c,inner). Next node chain[k+1] tells the step taken.
    if(k>=chain.size()) break;
    if(NX[a][c]<0){ return 0; }
    int w=W[a][c], d=D[a][c], a2=NX[a][c];
    bool isLast = (k+1==chain.size());
    if(d<0){ if(isLast){ if(haltEsc>=0){ allowPhi.insert(haltEsc); return 1; } why="top derivation ends on a left move"; return 2; }
      Tape ni; ni.push_back(w); ni.insert(ni.end(),inner.begin(),inner.end()); trim(ni); inner.swap(ni); a=a2; c=0; continue; }
    // a call
    Tape Y=inner; Tape Y2=Y; int o=sim(Y2,a2,TOPCAP); trim(Y2);
    if(o==6) return 0;
    long cc; Res fr;
    if(isLast){ if(haltDirect){ why="top halting node mismatch"; return 2; } cc=haltIc; fr=Res{6,0}; }
    else { cc=topn[chain[k+1]].ic; fr=topn[chain[k+1]].ir; if(topn[chain[k+1]].kind!=2){ why="top derivation kind mismatch"; return 2; } }
    bool match = (fr.s!=6) && o==fr.s && foldOf(Y2)==fr.q;
    if(!match){ if(o==7){ why="real trip longer than TOPCAP"; return 2; }
      Tape X; lastEsc=-1; sameClass=false; int rc=witness(cc,fr,X,0); if(rc==2 && sameClass && lastEsc>=0){ allowPhi.insert(lastEsc); return 1; } if(rc) return rc;
      if(separate(Y,X,a2)) return 1; if(sameClass && lastEsc>=0){ allowPhi.insert(lastEsc); return 1; } return 2; }
    c=w; inner.swap(Y2); a=o; }
  why="top derivation replayed without a halt"; return 2; }
int main(int argc,char**argv){
  char*m=argv[1]; bool mirror=argv[2][0]=='R'; long LS= argc>3? atol(argv[3]):1000000; if(argc>4) CAP=atol(argv[4]); long MAXR= argc>5? atol(argv[5]):5000; long MAXC= argc>6? atol(argv[6]):50000;
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*x=m+7*s+3*b; if(x[0]=='-'){NX[s][b]=-1;continue;} W[s][b]=x[0]-'0'; D[s][b]=x[1]=='R'?1:-1; if(mirror)D[s][b]=-D[s][b]; NX[s][b]=x[2]-'A';}
  for(int s=0;s<6;s++){ einIdx[s]=E.size(); E.push_back(expIn(s)); }
  { Tape bl; int q0=classOfRow(rowOf(bl),bl); phimemo[0]=q0; U[q0].push_back({0,q0}); }
  auto t0=chrono::steady_clock::now(); const char*verdict="ROUNDS"; long r=0; int nl=0;
  for(;r<MAXR;r++){
    while(learnPass(LS)) nl++;
    obsPass(LS);
    int rc=runDecider(MAXC);
    if(rc==0){ verdict="NONHALT"; break; } if(rc==2){ verdict="LIMIT"; break; }
    int cz=concretize();
    if(cz==0){ verdict="REAL-HALT"; break; } if(cz==2){ verdict="STUCK"; break; }
    if(r%20==0){ size_t nf=0; for(auto&kv:Sum) nf+=kv.second.size(); fprintf(stderr,"round %ld: exps=%zu classes=%zu realclasses=%zu allowed=%zu contracts=%zu facts=%zu top=%zu learnrefs=%d %.0fs\n",r,E.size(),cls.size(),exCls.size(),allowPhi.size(),known.size(),nf,topn.size(),nl,chrono::duration<double>(chrono::steady_clock::now()-t0).count()); }
  }
  size_t nf=0; for(auto&kv:Sum) nf+=kv.second.size(); size_t mw=0; for(auto&e:E){ size_t l=0; for(auto&pr:e.st) l+=pr.first.size(); mw=max(mw,l); }
  printf("%s %c : %s rounds=%ld exps=%zu classes=%zu realclasses=%zu allowed=%zu contracts=%zu facts=%zu top=%zu longest_exp=%zu sims=%ld time=%.0fs %s\n",m,argv[2][0],verdict,r,E.size(),cls.size(),exCls.size(),allowPhi.size(),known.size(),nf,topn.size(),mw,nsim,chrono::duration<double>(chrono::steady_clock::now()-t0).count(),why.c_str());
  return 0; }
