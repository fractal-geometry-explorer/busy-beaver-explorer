// endsplit: call-summary decider on a product automaton of half tapes:
//   (learned class of learncls) x (the whole tape if it has at most L cells, else its first K cells).
// Only the classes of short tapes (the end words) are split; the learned classes are frozen for the rest.
// The class of a half tape is a fold from its far end, so ANY such automaton gives a sound abstraction; the
// learned rows only decide how precise it is. Summaries (entry state, class) -> set of (return state, class) and
// the top level (left frontier, blank to its left) grow to a least fixed point. A class is unfolded only into
// the (cell, class) pairs that the fixed point itself produced. If no halting transition is derivable, the
// machine does not halt.
// Usage: [LEARN=<steps>] [TW=<cells>] [NOEXP=1] [WIN=<cells> WSTEPS=<steps>] endsplit MACHINE L|R LEX K [CAP] [MAXSTATES] [DUMP]
//   LEARN   learn classes from that many steps of the real run (as learncls.cpp); without it the classes are the
//           rows of the six one-entry experiments, and with NOEXP=1 there is one learned class only
//   TW      exact window of that many cells at the frontier (default 1: only the head cell is exact)
//   LEX     a half tape with at most LEX cells before the blank is its own class (the far end word)
//   K       longer half tapes are split by their first K cells
//   WIN     instead of LEX and K: split by the longest prefix that is a factor of a WIN-cell frontier window
//           seen in the first WSTEPS steps of the real run
// fwdec.cpp is the fast version of the case NOEXP=1, LEX=0. The DUMP file is read by check_cert.py.
#include <bits/stdc++.h>
using namespace std;
typedef vector<uint8_t> Tape;
static int W[6][2],D[6][2],NX[6][2];
static long CAP=2000000;
struct Exp { Tape w; int s; };
static vector<Exp> E;
static int sim(Tape &t,int s){ long p=0; for(long i=0;i<CAP;i++){ if(p>=(long)t.size()) t.resize(p+1,0); int b=t[p]; if(NX[s][b]<0) return 6; t[p]=W[s][b]; int d=D[s][b]; s=NX[s][b]; p+=d; if(p<0) return s; } return 7; }
static void trim(Tape&t){ while(!t.empty()&&t.back()==0) t.pop_back(); }
struct Cls { Tape rep; string row; };
static vector<Cls> cls; static unordered_map<string,int> rowmap; static long nsim=0;
static int classify(const Tape&x){ string row; Tape t;
  for(auto&e:E){ t.assign(e.w.begin(),e.w.end()); t.insert(t.end(),x.begin(),x.end()); int o=sim(t,e.s); nsim++; row.push_back((char)('0'+o)); }
  auto it=rowmap.find(row); if(it!=rowmap.end()) return it->second;
  int id=cls.size(); cls.push_back({x,row}); rowmap[row]=id; return id; }
static unordered_map<long,int> phimemo;
static int lphi(int c,int q){ long k=(long)q*2+c; auto it=phimemo.find(k); if(it!=phimemo.end()) return it->second;
  Tape t; t.push_back(c); t.insert(t.end(),cls[q].rep.begin(),cls[q].rep.end()); trim(t);
  int r=classify(t); phimemo[k]=r; return r; }
static int einIdx[6];
static void addExperiment(const Exp&e){ E.push_back(e); Tape t; rowmap.clear(); size_t n0=cls.size(); vector<string> oldrow(n0);
  for(size_t q=0;q<n0;q++){ oldrow[q]=cls[q].row; t.assign(e.w.begin(),e.w.end()); t.insert(t.end(),cls[q].rep.begin(),cls[q].rep.end()); int o=sim(t,e.s); nsim++; cls[q].row.push_back((char)('0'+o)); rowmap[cls[q].row]=q; }
  vector<pair<long,int>> ents(phimemo.begin(),phimemo.end()); sort(ents.begin(),ents.end());
  for(auto&kv:ents){ int c=kv.first%2; int q=kv.first/2; int r=kv.second; if((size_t)q>=n0||(size_t)r>=n0) continue;
    Tape x; x.push_back(c); x.insert(x.end(),cls[q].rep.begin(),cls[q].rep.end()); trim(x);
    t.assign(e.w.begin(),e.w.end()); t.insert(t.end(),x.begin(),x.end()); int o=sim(t,e.s); nsim++;
    string nr=oldrow[r]; nr.push_back((char)('0'+o)); if(nr==cls[r].row) continue;
    auto it=rowmap.find(nr); int id; if(it!=rowmap.end()) id=it->second; else { id=cls.size(); cls.push_back({x,nr}); rowmap[nr]=id; }
    phimemo[kv.first]=id; } }
static bool learnPass(long NS,int q0,long &cexStep){
  long T=1L<<25; static vector<uint8_t> tape; tape.assign(T,0); static vector<int> C; C.assign(T,q0);
  struct Fr{ long b; int s; int cl; long t0; }; vector<Fr> st; long p=T/2; int s=0; long hi=p; long bad_t0=-1,bad_b=-1; int bad_s=-1;
  for(long i=0;i<NS;i++){ int b=tape[p]; if(NX[s][b]<0) break; tape[p]=W[s][b]; int d=D[s][b]; s=NX[s][b]; long op=p; p+=d; if(p>hi)hi=p;
    if(d>0) st.push_back({op,s,C[op],i});
    else { C[op-1]=lphi(tape[op],C[op]);
      if(!st.empty()){ Fr f=st.back(); st.pop_back(); int pred=cls[f.cl].row[einIdx[f.s]]-'0'; if(pred!=s && i-f.t0<CAP/2){ bad_t0=f.t0; bad_b=f.b; bad_s=f.s; break; } } } }
  if(bad_t0<0) return false;
  tape.assign(T,0); p=T/2; s=0; hi=p;
  for(long i=0;i<=bad_t0;i++){ int b=tape[p]; tape[p]=W[s][b]; int d=D[s][b]; s=NX[s][b]; p+=d; if(p>hi)hi=p; }
  Tape t(tape.begin()+bad_b+1, tape.begin()+hi+2); trim(t); int n=t.size();
  vector<int> f(n+1); f[n]=q0; for(int i=n-1;i>=0;i--) f[i]=lphi(t[i],f[i+1]);
  int prev=-1; Tape x;
  for(int i=0;i<=n;i++){ x.assign(t.begin(),t.begin()+i); x.insert(x.end(),cls[f[i]].rep.begin(),cls[f[i]].rep.end()); int o=sim(x,bad_s); nsim++;
    if(i>0 && o!=prev){ Exp e; e.w.assign(t.begin(),t.begin()+(i-1)); e.s=bad_s; addExperiment(e); cexStep=bad_t0; return true; }
    prev=o; }
  cexStep=-bad_t0; return true; }
// ---------- product automaton ----------
static int LEX=0, KPRE=0, WIN=0; static unordered_set<string> PF; // PF: all factors of the end windows seen in the real run
struct PS { int l; bool exact; string w; };
static vector<PS> ps; static unordered_map<string,int> psmap;
static int psid(int l,bool exact,const string&w){ string k=to_string(l); k.push_back(exact?'e':'p'); k+=w; auto it=psmap.find(k); if(it!=psmap.end()) return it->second; int id=ps.size(); ps.push_back({l,exact,w}); psmap[k]=id; return id; }
static unordered_map<long,int> pmemo;
static int pphi(int c,int q){ long k=(long)q*2+c; auto it=pmemo.find(k); if(it!=pmemo.end()) return it->second;
  const PS p=ps[q]; int l=lphi(c,p.l); string w; w.push_back((char)('0'+c)); w+=p.w; int r;
  if(WIN>0){ while(!w.empty() && !PF.count(w)) w.pop_back(); r=psid(l,false,w); }
  else if(p.exact){ if(c==0&&p.w.empty()) r=q; else if((int)w.size()<=LEX) r=psid(l,true,w); else r=psid(l,false,w.substr(0,KPRE)); }
  else r=psid(l,false,w.substr(0,KPRE));
  pmemo[k]=r; return r; }
// ---------- decider ----------
struct Key { int s,q; bool operator==(const Key&o)const{return s==o.s&&q==o.q;} };
struct KH { size_t operator()(const Key&k)const{ return (size_t)k.q*7+k.s; } };
static unordered_map<Key,set<pair<int,int>>,KH> Sum; static unordered_map<Key,set<long>,KH> deps;
static unordered_map<int,set<long>> udeps; static vector<set<pair<int,int>>> U;
static deque<long> work; static unordered_set<long> inwork, known;
static inline long enc(int s,int q){ return (long)q*6+s; }
static void push(long c){ if(inwork.insert(c).second) work.push_back(c); }
static void need(long c){ if(known.insert(c).second) push(c); }
static long ntrans=0;
static int mk(int c,int qi){ int r=pphi(c,qi); if((int)U.size()<=r) U.resize(r+1); if(U[r].insert({c,qi}).second){ ntrans++; auto it=udeps.find(r); if(it!=udeps.end()) for(long d:it->second) push(d); } return r; }
static vector<array<int,4>> newfacts; static bool halted=false; static string haltinfo;
static string desc(int q){ return "["+to_string(ps[q].l)+(ps[q].exact?" =":" ~")+ps[q].w+"]"; }
static void evalc(long id){ int s=id%6, q=id/6; udeps[q].insert(id);
  set<tuple<int,int,int>> seen; vector<tuple<int,int,int>> st;
  if((int)U.size()<=q) U.resize(q+1);
  { vector<pair<int,int>> u(U[q].begin(),U[q].end()); for(auto&x:u){ auto m=make_tuple(s,x.first,x.second); if(seen.insert(m).second) st.push_back(m); } }
  bool changed=false;
  while(!st.empty()){ auto [a,c1,qi]=st.back(); st.pop_back();
    if(NX[a][c1]<0){ halted=true; haltinfo="contract s="+string(1,'A'+s)+" q="+desc(q)+" micro "+string(1,'A'+a)+to_string(c1)+" inner "+desc(qi); return; }
    int w=W[a][c1], d=D[a][c1], a2=NX[a][c1];
    if(d<0){ int r=mk(w,qi); if(Sum[{s,q}].insert({a2,r}).second){ changed=true; newfacts.push_back({s,q,a2,r}); } }
    else { long cc=enc(a2,qi); need(cc); deps[{a2,qi}].insert(id);
      auto it=Sum.find({a2,qi}); if(it!=Sum.end()) { vector<pair<int,int>> tmp(it->second.begin(),it->second.end()); for(auto&pr:tmp){ auto m=make_tuple(pr.first,w,pr.second); if(seen.insert(m).second) st.push_back(m); } } } }
  if(changed) for(long d_:deps[{s,q}]) push(d_); }
// top level: an exact window of TW cells from the left frontier, head inside, class q for the rest
static int TW=1;
struct TN { int a,i,q; string win; };
static vector<TN> topn; static unordered_map<string,int> topseen; static vector<int> topst; static unordered_map<Key,vector<int>,KH> topwait;
static void addtop(int a,int i,const string&win,int q){ string k=win; k.push_back((char)('A'+a)); k+=to_string(i); k.push_back(','); k+=to_string(q);
  if(topseen.emplace(k,(int)topn.size()).second){ topn.push_back({a,i,q,win}); topst.push_back(topn.size()-1); } }
static void topret(int ix,int s2,int q2){ TN n=topn[ix]; int c=n.win[n.i]-'0'; string w=n.win; w[n.i]='0'+W[n.a][c]; addtop(s2,TW-1,w,q2); }
static void evaltop(){
  while(!topst.empty()){ int ix=topst.back(); topst.pop_back(); TN n=topn[ix]; int a=n.a, c=n.win[n.i]-'0';
    if(NX[a][c]<0){ halted=true; haltinfo="top "+string(1,'A'+a)+to_string(c)+" pos "+to_string(n.i)+" win "+n.win+" q="+desc(n.q); return; }
    int w=W[a][c], d=D[a][c], a2=NX[a][c]; string win=n.win; win[n.i]='0'+w;
    if(d<0){ if(n.i>0) addtop(a2,n.i-1,win,n.q); else { int q2=mk(win[TW-1]-'0',n.q); addtop(a2,0,"0"+win.substr(0,TW-1),q2); } }
    else if(n.i<TW-1) addtop(a2,n.i+1,win,n.q);
    else { need(enc(a2,n.q)); topwait[{a2,n.q}].push_back(ix);
      auto it=Sum.find({a2,n.q}); if(it!=Sum.end()){ vector<pair<int,int>> tmp(it->second.begin(),it->second.end()); for(auto&pr:tmp) topret(ix,pr.first,pr.second); } } } }
int main(int argc,char**argv){
  char*m=argv[1]; bool mirror=argv[2][0]=='R'; LEX=atoi(argv[3]); KPRE=atoi(argv[4]); if(argc>5) CAP=atol(argv[5]); long MAXS= argc>6? atol(argv[6]):2000000; const char*dump= argc>7? argv[7]:0;
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*x=m+7*s+3*b; if(x[0]=='-'){NX[s][b]=-1;continue;} W[s][b]=x[0]-'0'; D[s][b]=x[1]=='R'?1:-1; if(mirror)D[s][b]=-D[s][b]; NX[s][b]=x[2]-'A';}
  long LS= getenv("LEARN")? atol(getenv("LEARN")):0;
  if(!getenv("NOEXP")) for(int s=0;s<6;s++){ einIdx[s]=E.size(); E.push_back({Tape(),s}); }
  int q0=classify(Tape()); phimemo[(long)q0*2+0]=q0;
  int rounds=0; for(;LS>0&&rounds<100000;rounds++){ long cs=0; if(!learnPass(LS,q0,cs)) break; if(cs<0) break; if((long)cls.size()>200000) break; }
  size_t nl=cls.size();
  if(getenv("WIN")){ WIN=atoi(getenv("WIN")); long NW=atol(getenv("WSTEPS")? getenv("WSTEPS"):"3000000"); long T=1L<<26; vector<uint8_t> tape(T,0); long p=T/2,lo=p; int s=0; unordered_set<string> wins; string cur;
    tape.assign(T,0); p=T/2; lo=p; s=0;
    for(long i=0;i<NW;i++){ int b=tape[p]; if(NX[s][b]<0) break; int d=D[s][b]; tape[p]=W[s][b]; s=NX[s][b]; long op=p; p+=d; if(p<lo) lo=p;
      if(op<lo+WIN){ cur.resize(WIN); for(int j=0;j<WIN;j++) cur[j]='0'+tape[lo+j]; wins.insert(cur); } }
    for(auto&w:wins) for(int i=0;i<WIN;i++) for(int j=1;i+j<=WIN;j++) PF.insert(w.substr(i,j));
    fprintf(stderr,"windows=%zu factors=%zu\n",wins.size(),PF.size()); }
  int p0=psid(q0,WIN==0,""); U.resize(1); U[p0].insert({0,p0}); pmemo[(long)p0*2]=p0;
  if(getenv("TW")) TW=atoi(getenv("TW")); addtop(0,0,string(TW,'0'),p0); push(-1);
  auto t0=chrono::steady_clock::now(); long it=0; bool limit=false;
  while(!work.empty()){ long c=work.front(); work.pop_front(); inwork.erase(c); it++;
    if(c==-1) evaltop(); else evalc(c);
    if(!halted && !newfacts.empty()){ vector<array<int,4>> nf; nf.swap(newfacts); for(auto&f:nf){ auto itw=topwait.find({f[0],f[1]}); if(itw==topwait.end()) continue; vector<int> ws=itw->second; for(int ix:ws) topret(ix,f[2],f[3]); } }
    if(!topst.empty()) push(-1);
    if(halted) break; if((long)ps.size()>MAXS){ limit=true; break; }
    if(it%2000000==0) fprintf(stderr,"  it=%ld states=%zu contracts=%zu work=%zu\n",it,ps.size(),known.size(),work.size()); }
  size_t nsum=0; for(auto&kv:Sum) nsum+=kv.second.size();
  printf("%s %c TW=%d L=%d K=%d learn=%ld : %s  learned=%zu(now %zu) exps=%zu states=%zu trans=%ld contracts=%zu facts=%zu top=%zu %.1fs %s\n",m,argv[2][0],TW,LEX,KPRE,LS, halted?"HALT-REACHABLE":(limit?"LIMIT":"NONHALT"), nl,cls.size(),E.size(),ps.size(),ntrans,known.size(),nsum,topn.size(),chrono::duration<double>(chrono::steady_clock::now()-t0).count(),haltinfo.c_str());
  if(dump && !halted && !limit){ FILE*f=fopen(dump,"w"); fprintf(f,"machine %s %c\nstates %zu\n",m,argv[2][0],ps.size());
    for(size_t r=0;r<U.size();r++) for(auto&x:U[r]) fprintf(f,"T %d %d %zu\n",x.first,x.second,r);
    for(auto&kv:Sum) for(auto&x:kv.second) fprintf(f,"F %d %d %d %d\n",kv.first.s,kv.first.q,x.first,x.second);
    for(auto&x:topn) fprintf(f,"P %d %d %s %d\n",x.a,x.i,x.win.c_str(),x.q); fclose(f); }
  return 0; }
