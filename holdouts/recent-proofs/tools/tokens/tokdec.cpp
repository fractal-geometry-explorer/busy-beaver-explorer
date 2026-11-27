// tokdec: call-summary decider over a token abstraction of half tapes.
//
// The machine is mirrored if needed so that the regular end of the tape is the left end.
// A half tape (the cells right of some boundary, nearest cell first) is abstracted by
//   - its first R maximal runs, each run length kept exactly below CAPL and as ">= CAPL with known parity" above
//     (these are the tokens), and
//   - the class q of the rest, where classes are the states of an automaton that reads the rest from its far end.
//     The classes are learned from the real run as rows of an observation table (same learner as
//     ../writeonly/learncls.cpp), or there is a single class when LEARN=0.
// G is the set of abstract half tapes that can occur right of any boundary. A call (ctx, s, a) is the head in
// state s on the first cell of an abstract half tape a, with a left context ctx: the last J maximal runs to its
// left, lengths capped in the same way. The call returns when the head leaves ctx to the left; its summary is
// the set of (return state, abstract half tape right of the left edge of ctx afterwards). While a call is
// evaluated the head moves over the context exactly; when a move to the right makes the context longer than J
// runs, the nearest J runs become the context of a nested call.
// The top level keeps the first W cells from the leftmost 1 of the tape exactly, and treats every exit to the
// right of them as a call. Least fixed point; if no halting transition is reachable in it the machine never halts
// (induction on the step budget, as for sumdec.py).
//
// Usage: [LEARN=steps] [RESK=k] [J=runs] [AUTO=file] [REAL=steps] tokdec MACHINE L|R R CAPL W [SIMCAP] [MAXNODES]
#include <bits/stdc++.h>
using namespace std;
typedef vector<uint8_t> Tape;
static int Wr[6][2],Dr[6][2],NX[6][2];
static long CAP=200000; static int RESK=0;
// ---------- learned classes (observation table) ----------
struct Exp { Tape w; int s; };
static vector<Exp> E;
static int sim(Tape &t,int s){ long p=0; for(long i=0;i<CAP;i++){ if(p>=(long)t.size()) t.resize(p+1,0); int b=t[p]; if(NX[s][b]<0) return 6; t[p]=Wr[s][b]; int d=Dr[s][b]; s=NX[s][b]; p+=d; if(p<0) return s; } return 7; }
static void trim(Tape&t){ while(!t.empty()&&t.back()==0) t.pop_back(); }
struct Cls { Tape rep; string row; };
static vector<Cls> cls; static unordered_map<string,int> rowmap; static long nsim=0;
static int classify(const Tape&x){
  string row; Tape t;
  for(auto&e:E){ t.assign(e.w.begin(),e.w.end()); t.insert(t.end(),x.begin(),x.end()); int o=sim(t,e.s); nsim++; row.push_back((char)('0'+o));
    for(int j=0;j<RESK;j++) row.push_back(o<6 && j<(int)t.size()? (char)('a'+t[j]) : (o<6?'a':'x')); }
  auto it=rowmap.find(row); if(it!=rowmap.end()) return it->second;
  int id=cls.size(); cls.push_back({x,row}); rowmap[row]=id; return id;
}
static unordered_map<long,int> phimemo;
static int phi(int c,int q){ long k=(long)q*2+c; auto it=phimemo.find(k); if(it!=phimemo.end()) return it->second;
  Tape t; t.push_back(c); t.insert(t.end(),cls[q].rep.begin(),cls[q].rep.end()); trim(t);
  int r=classify(t); phimemo[k]=r; return r; }
static int einIdx[6];
static void addExperiment(const Exp&e){
  E.push_back(e); Tape t; rowmap.clear(); size_t n0=cls.size(); vector<string> oldrow(n0);
  auto ext=[&](const Tape&x){ string add; t.assign(e.w.begin(),e.w.end()); t.insert(t.end(),x.begin(),x.end()); int o=sim(t,e.s); nsim++; add.push_back((char)('0'+o));
    for(int j=0;j<RESK;j++) add.push_back(o<6 && j<(int)t.size()? (char)('a'+t[j]) : (o<6?'a':'x')); return add; };
  for(size_t q=0;q<n0;q++){ oldrow[q]=cls[q].row; cls[q].row+=ext(cls[q].rep); rowmap[cls[q].row]=q; }
  vector<pair<long,int>> ents(phimemo.begin(),phimemo.end());
  for(auto&kv:ents){ int c=kv.first%2; int q=kv.first/2; int r=kv.second; if((size_t)q>=n0||(size_t)r>=n0) continue;
    Tape x; x.push_back(c); x.insert(x.end(),cls[q].rep.begin(),cls[q].rep.end()); trim(x);
    string nr=oldrow[r]+ext(x);
    if(nr==cls[r].row) continue;
    auto it=rowmap.find(nr); int id; if(it!=rowmap.end()) id=it->second; else { id=cls.size(); cls.push_back({x,nr}); rowmap[nr]=id; }
    phimemo[kv.first]=id; }
}
static bool learnPass(long NS,int q0,long &cexStep){
  long T=1L<<25; static vector<uint8_t> tape; tape.assign(T,0); static vector<int> C; C.assign(T,q0);
  struct Fr{ long b; int s; int cl; long t0; }; vector<Fr> st; long p=T/2; int s=0; long hi=p;
  long bad_t0=-1, bad_b=-1; int bad_s=-1;
  for(long i=0;i<NS;i++){ int b=tape[p]; if(NX[s][b]<0) break; tape[p]=Wr[s][b]; int d=Dr[s][b]; s=NX[s][b]; long op=p; p+=d; if(p>hi)hi=p;
    if(d>0){ st.push_back({op,s,C[op],i}); }
    else { C[op-1]=phi(tape[op],C[op]);
      if(!st.empty()){ Fr f=st.back(); st.pop_back(); if(einIdx[f.s]<0){ bad_t0=f.t0; bad_b=f.b; bad_s=f.s; break; }
        const string&row=cls[f.cl].row; int base=einIdx[f.s]*(1+RESK); int pred=row[base]-'0'; bool bad=pred!=s;
        for(int j=0;j<RESK&&!bad;j++) if(row[base+1+j]!=(char)('a'+tape[op+j])) bad=true;
        if(bad && i-f.t0<CAP/2){ bad_t0=f.t0; bad_b=f.b; bad_s=f.s; break; } } }
  }
  if(bad_t0<0) return false;
  tape.assign(T,0); p=T/2; s=0; hi=p;
  for(long i=0;i<=bad_t0;i++){ int b=tape[p]; tape[p]=Wr[s][b]; int d=Dr[s][b]; s=NX[s][b]; p+=d; if(p>hi)hi=p; }
  Tape t(tape.begin()+bad_b+1, tape.begin()+hi+2); trim(t); int n=t.size();
  if(einIdx[bad_s]<0){ Exp e; e.s=bad_s; einIdx[bad_s]=E.size(); addExperiment(e); cexStep=bad_t0; return true; }
  vector<int> f(n+1); f[n]=q0; for(int i=n-1;i>=0;i--) f[i]=phi(t[i],f[i+1]);
  string prev; Tape x; int ei=einIdx[bad_s];
  for(int i=0;i<=n;i++){ x.assign(t.begin(),t.begin()+i); x.insert(x.end(),cls[f[i]].rep.begin(),cls[f[i]].rep.end()); int o=sim(x,bad_s); nsim++;
    string cur; cur.push_back('0'+o); for(int j=0;j<RESK;j++) cur.push_back(o<6 && j<(int)x.size()? (char)('a'+x[j]) : (o<6?'a':'x'));
    if(i>0 && cur!=prev){ Exp e; e.w.assign(t.begin(),t.begin()+(i-1)); e.s=bad_s; addExperiment(e); cexStep=bad_t0; return true; }
    prev=cur; }
  (void)ei; cexStep=-bad_t0-1; return true;
}
// ---------- abstract half tapes ----------
static int R=2, CAPL=4;
struct El { uint8_t b0; vector<uint8_t> len; int q; };   // runs alternate starting with bit b0; len code: 1..CAPL-1 exact, CAPL+par = ">=CAPL, parity par"
static vector<El> els; static unordered_map<string,int> elmap; static int q0=0, BLANK=0;
static int intern(const El&e){ string k; k.push_back(e.b0); k.append(e.len.begin(),e.len.end()); k.push_back((char)255); k.append((const char*)&e.q,4);
  auto it=elmap.find(k); if(it!=elmap.end()) return it->second; int id=els.size(); els.push_back(e); elmap[k]=id; return id; }
static inline uint8_t incLen(uint8_t L){ if(L<CAPL-1) return L+1; if(L==CAPL-1) return CAPL+(CAPL&1); return CAPL+((L-CAPL)^1); }
static void foldRun(int bit,uint8_t L,int q,vector<int>&out){ // classes of bit^n . rest for all n matching the code
  if(L<CAPL){ for(int i=0;i<L;i++) q=phi(bit,q); out.push_back(q); return; }
  int par=L-CAPL; for(int i=0;i<CAPL;i++) q=phi(bit,q); int n=CAPL;
  set<pair<int,int>> seen; set<int> res;
  while(seen.insert({q,n&1}).second){ if((n&1)==par) res.insert(q); q=phi(bit,q); n++; }
  out.assign(res.begin(),res.end()); }
static unordered_map<long,vector<int>> consmemo;
static const vector<int>& Cons(int c,int a){ long k=(long)a*2+c; auto it=consmemo.find(k); if(it!=consmemo.end()) return it->second;
  vector<int> out; El e=els[a];
  if(e.len.empty()){ if(c==0) out.push_back(a); else { El n; n.b0=1; n.len={1}; n.q=q0; out.push_back(intern(n)); } }
  else if(e.b0==c){ e.len[0]=incLen(e.len[0]); out.push_back(intern(e)); }
  else { El n; n.b0=c; n.len.push_back(1); n.len.insert(n.len.end(),e.len.begin(),e.len.end()); n.q=e.q;
    if((int)n.len.size()>R){ uint8_t L=n.len.back(); n.len.pop_back(); int bit=(n.b0^((int)n.len.size()&1)); vector<int> qs; foldRun(bit,L,e.q,qs);
      for(int q:qs){ n.q=q; out.push_back(intern(n)); } }
    else out.push_back(intern(n)); }
  return consmemo[k]=out; }
// ---------- left contexts: runs nearest the head first ----------
static int J=0;
struct Lc { uint8_t b0; vector<uint8_t> len; };
static vector<Lc> lcs; static unordered_map<string,int> lcmap;
static int internL(const Lc&e){ string k; k.push_back(e.len.empty()?0:e.b0); k.append(e.len.begin(),e.len.end());
  auto it=lcmap.find(k); if(it!=lcmap.end()) return it->second; int id=lcs.size(); lcs.push_back(e); if(e.len.empty()) lcs.back().b0=0; lcmap[k]=id; return id; }
static int pushL(int l,int c){ Lc e=lcs[l]; if(!e.len.empty()&&e.b0==c) e.len[0]=incLen(e.len[0]); else { e.len.insert(e.len.begin(),1); e.b0=c; } return internL(e); }
static void popL(int l,vector<int>&out){ // contexts after removing the cell nearest the head (which is bit lcs[l].b0)
  Lc e=lcs[l]; uint8_t L=e.len[0];
  if(L>=CAPL){ int par=L-CAPL; Lc f=e; f.len[0]=CAPL+(par^1); out.push_back(internL(f)); if(((CAPL-1)&1)==(par^1)){ L=CAPL; } else return; }
  if(L>1){ e.len[0]=L-1; out.push_back(internL(e)); } else { e.len.erase(e.len.begin()); e.b0^=1; out.push_back(internL(e)); } }
static string lcstr(int l){ const Lc&e=lcs[l]; string r="<"; int bit=e.b0; for(size_t i=0;i<e.len.size();i++){ if(i) r+=' '; r+=to_string(bit); r+='^'; if(e.len[i]<CAPL) r+=to_string(e.len[i]); else r+=string(">=")+to_string(CAPL)+((e.len[i]-CAPL)?"odd":"even"); bit^=1; } return r+">"; }
// ---------- fixed point ----------
static vector<char> inG; static vector<vector<int>> inv; static vector<vector<int>> udeps; // per element: nodes that unfolded it
struct Node { int kind; int s,a; string x; int h; int l; };  // kind 0 = contract (s,a), 1 = top config
static vector<Node> nodes; static unordered_map<string,int> nodemap;
static vector<set<pair<int,int>>> Sum; static vector<vector<int>> deps; // per contract node: results, dependents
static deque<int> work; static vector<char> inwork;
static bool halted=false; static string haltinfo; static long ntop=0,ncon=0;
static void push(int n){ if(!inwork[n]){ inwork[n]=1; work.push_back(n); } }
static void growEl(){ size_t n=els.size(); if(inG.size()<n){ inG.resize(n,0); inv.resize(n); udeps.resize(n); } }
static vector<int> gorder; static vector<tuple<int,int,int,int,int,int>> forder; static int curNode=-1;
static vector<string> gwhy; static string curWhy;
static string elstr(int a); static const char*WATCH=0; static int nwatch=0;
static void addG(int a){ growEl(); if(inG[a]) return; inG[a]=1; gorder.push_back(a);
  if(WATCH&&nwatch<8&&elstr(a).find(WATCH)!=string::npos){ nwatch++; printf("WATCH %s  <= %s\n",elstr(a).c_str(),curWhy.c_str()); }
  for(int c=0;c<2;c++){ vector<int> r=Cons(c,a); growEl(); for(int a2:r){ inv[a2].push_back(a); for(int n:udeps[a2]) push(n); } } }
static int nodeId(const Node&nd){ string k; k.push_back('0'+nd.kind); k.push_back('A'+nd.s); k.append((const char*)&nd.a,4); k.append((const char*)&nd.l,4); if(nd.kind){ k.append((const char*)&nd.h,4); k+=nd.x; }
  auto it=nodemap.find(k); if(it!=nodemap.end()) return it->second; int id=nodes.size(); nodes.push_back(nd); nodemap[k]=id; Sum.emplace_back(); deps.emplace_back(); inwork.push_back(0);
  if(nd.kind) ntop++; else ncon++; push(id); return id; }
static int contract(int l,int s,int a){ Node nd; nd.kind=0; nd.s=s; nd.a=a; nd.h=0; nd.l=l; return nodeId(nd); }
static void adddep(int c,int n){ auto&v=deps[c]; if(find(v.begin(),v.end(),n)==v.end()) v.push_back(n); }
static void addudep(int a,int n){ growEl(); auto&v=udeps[a]; if(find(v.begin(),v.end(),n)==v.end()) v.push_back(n); }
static string elstr(int a);
static int EMPTYL=0;
// ---------- diagnostics: the abstract image of the real run ----------
static bool DIAG=false; static set<int> realG; static set<array<int,6>> realMicro; static set<array<int,5>> realFact; static set<string> realTop;
static set<string> reported; static int nrep=0; static bool parentReal=false; static string parentStr, viaStr; static array<int,3> curKey;
static void report(const string&what){ if(nrep>=60) return; string m=what+"   <= "+parentStr+"   ["+viaStr+"]"; if(reported.insert(m).second){ nrep++; printf("  first-wrong: %s\n",m.c_str()); } }
static void evalc(int id){ int s=nodes[id].s, a=nodes[id].a, l0=nodes[id].l;
  set<tuple<int,int,int>> seen; vector<tuple<int,int,int>> st;   // (context, state, half tape), head on the first cell of the half tape
  curKey={l0,s,a};
  auto add=[&](int l,int q,int b){ auto m=make_tuple(l,q,b); if(seen.insert(m).second) st.push_back(m);
    if(DIAG&&parentReal&&!realMicro.count({l0,s,a,l,q,b})) report("config "+lcstr(l)+" "+string(1,'A'+q)+" "+elstr(b)); };
  // the head has just moved left onto the nearest cell of context l (or out of the call if l is empty), with half tape b behind it
  auto landLeft=[&](int l,int q,int b,bool&changed){
    if(lcs[l].len.empty()){ addG(b); if(Sum[id].insert({q,b}).second){ changed=true; forder.emplace_back(id,q,b,0,0,0); }
      if(DIAG&&parentReal&&!realFact.count({l0,s,a,q,b})) report("return "+string(1,'A'+q)+" "+elstr(b)); return; }
    int x=lcs[l].b0; vector<int> ls; popL(l,ls); vector<int> bs=Cons(x,b); for(int b2:bs){ addG(b2); for(int l2:ls) add(l2,q,b2); } };
  add(l0,s,a);
  bool changed=false;
  while(!st.empty()){ auto [l,q,b]=st.back(); st.pop_back(); addudep(b,id);
    if(WATCH) curWhy="call "+lcstr(l0)+" "+string(1,'A'+s)+" "+elstr(a)+" at "+lcstr(l)+" "+string(1,'A'+q)+" "+elstr(b);
    if(DIAG){ parentReal=realMicro.count({l0,s,a,l,q,b}); parentStr="in call "+lcstr(l0)+" "+string(1,'A'+s)+" "+elstr(a)+" at "+lcstr(l)+" "+string(1,'A'+q)+" "+elstr(b); }
    int c1= els[b].len.empty()?0:els[b].b0; vector<int> iv=inv[b];
    if(NX[q][c1]<0){ if(iv.empty()) continue; halted=true; haltinfo="contract "+lcstr(l0)+" "+string(1,'A'+s)+" "+elstr(a)+" at "+lcstr(l)+" "+string(1,'A'+q)+" "+elstr(b); return; }
    int w=Wr[q][c1], d=Dr[q][c1], q2=NX[q][c1];
    bool pr0=parentReal;
    for(int b1:iv){ if(DIAG){ parentReal=pr0&&realG.count(b1); viaStr="rest "+elstr(b1); }
      if(d<0){ vector<int> rs=Cons(w,b1); for(int r:rs){ addG(r); landLeft(l,q2,r,changed); } }
      else { int l2=pushL(l,w);
        if((int)lcs[l2].len.size()<=J) add(l2,q2,b1);
        else { Lc in=lcs[l2]; Lc out; out.b0=in.b0^(J&1); out.len.assign(in.len.begin()+J,in.len.end()); in.len.resize(J); int lin=internL(in), lout=internL(out);
          int cc=contract(lin,q2,b1); adddep(cc,id);
          vector<pair<int,int>> tmp(Sum[cc].begin(),Sum[cc].end()); for(auto&pr:tmp){ if(DIAG){ parentReal=pr0&&realG.count(b1)&&realFact.count({lin,q2,b1,pr.first,pr.second}); viaStr="rest "+elstr(b1)+", nested call "+lcstr(lin)+" "+string(1,'A'+q2)+" returned "+string(1,'A'+pr.first)+" "+elstr(pr.second); }
            landLeft(lout,pr.first,pr.second,changed); } } } } }
  if(changed){ vector<int> dv=deps[id]; for(int d_:dv) push(d_); }
}
static int Wn=24; static bool gapfail=false;
static void emitTop(string x,int h,int s,int a){ // x normalised: starts with 1 or is empty
  if(x.empty()&&a==BLANK) h=0;
  if(a==BLANK){ while(!x.empty()&&x.back()=='0') x.pop_back(); }
  Node nd; nd.kind=1; nd.s=s; nd.a=a; nd.x=x; nd.h=h; nd.l=0; nodeId(nd); }
static void evaltop(int id){ Node nd=nodes[id]; string x=nd.x; int h=nd.h, s=nd.s, a=nd.a; int len=x.size();
  if(WATCH) curWhy="top x="+x+" h="+to_string(h)+" "+string(1,'A'+s)+" "+elstr(a);

  int c = (h>=0&&h<len)? x[h]-'0' : 0;
  if(NX[s][c]<0){ halted=true; haltinfo="top x="+x+" h="+to_string(h)+" state "+string(1,'A'+s)+" a="+elstr(a); return; }
  int w=Wr[s][c], d=Dr[s][c], s2=NX[s][c];
  // write
  vector<pair<string,pair<int,int>>> cands; // (x, (h, a)) after write and normalisation, before the move
  if(h>=0&&h<len){ x[h]='0'+w;
    if(x[0]=='0'){ size_t z=x.find('1'); if(z!=string::npos){ x=x.substr(z); h-=z; cands.push_back({x,{h,a}}); }
      else { // exact part is all zero: unfold a until a 1 appears
        int zeros=len; h-=zeros; set<pair<int,int>> seen; vector<pair<int,int>> st; st.push_back({a,0}); seen.insert({a,0});
        while(!st.empty()){ auto [b,z2]=st.back(); st.pop_back(); addudep(b,id);
          if(b==BLANK){ cands.push_back({"",{0,BLANK}}); continue; }
          if(z2>4*Wn+64){ gapfail=true; continue; }
          int cb=els[b].b0; vector<int> iv=inv[b];
          for(int b1:iv){ if(cb==1) cands.push_back({"1",{h-z2,b1}}); else if(seen.insert({b1,z2+1}).second) st.push_back({b1,z2+1}); } } } }
    else cands.push_back({x,{h,a}}); }
  else if(h<0){ if(w==1){ x=string("1")+string(-h-1,'0')+x; h=0; } cands.push_back({x,{h,a}}); }
  else { // h==len can only happen for the blank tape (len==0,h==0)
    if(w==1){ x="1"; h=0; } cands.push_back({x,{h,a}}); }
  for(auto&cd:cands){ string y=cd.first; int hh=cd.second.first; vector<int> as; as.push_back(cd.second.second);
    while((int)y.size()>Wn){ int cc=y.back()-'0'; y.pop_back(); vector<int> nas; for(int b:as){ vector<int> r=Cons(cc,b); for(int r1:r){ addG(r1); nas.push_back(r1); } } sort(nas.begin(),nas.end()); nas.erase(unique(nas.begin(),nas.end()),nas.end()); as=nas; }
    int ylen=y.size();
    for(int b:as){
      if(ylen==0){ emitTop(y,0,s2,b); continue; }
      int nh=hh+d;
      if(nh<ylen){ emitTop(y,nh,s2,b); continue; }
      int cc=contract(EMPTYL,s2,b); adddep(cc,id);
      vector<pair<int,int>> tmp(Sum[cc].begin(),Sum[cc].end()); for(auto&pr:tmp) emitTop(y,ylen-1,pr.first,pr.second); } }
}
static string elstr(int a){ const El&e=els[a]; string r="["; int bit=e.b0; for(size_t i=0;i<e.len.size();i++){ if(i) r+=' '; r+=to_string(bit); r+='^'; if(e.len[i]<CAPL) r+=to_string(e.len[i]); else r+=string(">=")+to_string(CAPL)+((e.len[i]-CAPL)?"odd":"even"); bit^=1; } r+=" | q"+to_string(e.q)+"]"; return r; }
static string topKey(const string&x,int h,int s,int a){ return x+" h="+to_string(h)+" "+string(1,'A'+s)+" "+to_string(a); }
static void realRun(long NS){
  long T=1L<<25; vector<uint8_t> tape(T,0); vector<int> Cq(T,q0); long p=T/2; int s=0; long hi=p, lo=p;
  auto code=[&](long L)->uint8_t{ return L<CAPL? L : CAPL+(L&1); };
  auto alpha=[&](long b)->int{ // abstraction of tape[b+1..]
    long i=b+1; while(hi>=i&&tape[hi]==0) hi--; if(hi<i){ if(hi<p) hi=p; return BLANK; }
    El e; e.b0=tape[i]; e.q=q0; int bit=tape[i];
    while(i<=hi && (int)e.len.size()<R){ long j=i; while(j<=hi&&tape[j]==bit) j++; e.len.push_back(code(j-i)); i=j; bit^=1; }
    if(i<=hi) e.q=Cq[i-1];
    if(R==0){ e.b0=tape[b+1]; e.q=Cq[b+1]; }
    return intern(e); };
  auto lam=[&](long B,long pp)->int{ // context: cells B+1..pp, nearest (pp) first
    Lc e; e.b0=0; if(pp<=B) return internL(e); e.b0=tape[pp]; long i=pp; int bit=tape[pp];
    while(i>B){ long j=i; while(j>B&&tape[j]==bit) j--; e.len.push_back(code(i-j)); i=j; bit^=1; } return internL(e); };
  struct Fr{ long B; int l,s,a; }; vector<Fr> st; realG.insert(BLANK);
  long Ex=p, Bt=p-1; bool blank=true;  // exact part of the top level = cells Ex..Bt
  for(long i=0;i<NS;i++){
    if(st.empty()){ string x; for(long j=Ex;j<=Bt;j++) x.push_back('0'+tape[j]); int a=alpha(Bt); if(a==BLANK){ while(!x.empty()&&x.back()=='0'){ x.pop_back(); Bt--; } }
      realTop.insert(topKey(x, x.empty()?0:(int)(p-Ex), s, a)); if(x.empty()){ blank=true; } }
    else { Fr&f=st.back(); realMicro.insert({f.l,f.s,f.a,lam(f.B,p-1),s,alpha(p-1)}); }
    int b=tape[p]; if(NX[s][b]<0) break; int w=Wr[s][b]; tape[p]=w; int d=Dr[s][b]; s=NX[s][b]; long op=p; p+=d; if(p>hi)hi=p; if(p<lo)lo=p;
    if(d<0) Cq[op-1]=phi(tape[op],Cq[op]);
    realG.insert(alpha(op-1)); realG.insert(alpha(op));
    if(st.empty()){
      if(blank){ if(w==1){ Ex=Bt=op; blank=false; } else { Ex=p; Bt=p-1; } }
      else if(op<Ex){ if(w==1){ Ex=op; if(Bt>Ex+Wn-1) Bt=Ex+Wn-1; } }
      else if(op==Ex&&w==0){ long j=Ex; while(j<=hi&&tape[j]==0) j++; if(j>hi){ blank=true; Ex=p; Bt=p-1; } else if(j<=Bt) Ex=j; else { Ex=Bt=j; } }
      if(!blank&&p>Bt){ st.push_back({Bt,EMPTYL,s,alpha(Bt)}); }
    } else {
      Fr f=st.back();
      if(d>0){ int l2=lam(f.B,op); if((int)lcs[l2].len.size()>J){ long j=op; int bit=tape[op]; for(int r=0;r<J;r++){ while(j>f.B&&tape[j]==bit) j--; bit^=1; } st.push_back({j,lam(j,op),s,alpha(op)}); } }
      else if(p==f.B){ realFact.insert({f.l,f.s,f.a,s,alpha(f.B)}); st.pop_back(); } }
  }
}
int main(int argc,char**argv){
  if(argc<6){ fprintf(stderr,"usage\n"); return 1; }
  char*m=argv[1]; bool mirror=argv[2][0]=='R'; R=atoi(argv[3]); CAPL=atoi(argv[4]); Wn=atoi(argv[5]); if(argc>6) CAP=atol(argv[6]); long MAXN= argc>7? atol(argv[7]):3000000;
  if(getenv("RESK")) RESK=atoi(getenv("RESK"));
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*x=m+7*s+3*b; if(x[0]=='-'){NX[s][b]=-1;continue;} Wr[s][b]=x[0]-'0'; Dr[s][b]=x[1]=='R'?1:-1; if(mirror)Dr[s][b]=-Dr[s][b]; NX[s][b]=x[2]-'A';}
  for(int z=0;z<6;z++) einIdx[z]=-1;
  if(getenv("AUTO")){ FILE*f=fopen(getenv("AUTO"),"r"); int n; if(!f||fscanf(f,"%d %d",&n,&q0)!=2){ fprintf(stderr,"bad AUTO\n"); return 1; }
    cls.resize(n); for(int q=0;q<n;q++){ int a,b; if(fscanf(f,"%d %d",&a,&b)!=2) return 1; phimemo[(long)q*2]=a; phimemo[(long)q*2+1]=b; } fclose(f); }
  else { q0=classify(Tape()); phimemo[(long)q0*2+0]=q0; }
  long LS= getenv("LEARN")? atol(getenv("LEARN")):0; int rounds=0; long last=0; long MAXC= getenv("MAXCLS")? atol(getenv("MAXCLS")):20000;
  if(LS>0){ for(;rounds<100000;rounds++){ long cs=0; if(!learnPass(LS,q0,cs)) break; last=cs; if(cs<0){ fprintf(stderr,"no change point at %ld\n",-cs-1); break; }
      if((long)cls.size()>MAXC) break; }
    size_t mw=0; for(auto&e:E) mw=max(mw,e.w.size());
    fprintf(stderr,"learned: rounds=%d exps=%zu classes=%zu longest w=%zu last cex step=%ld\n",rounds,E.size(),cls.size(),mw,last); }
  WATCH=getenv("WATCH"); if(getenv("J")) J=atoi(getenv("J")); { Lc e; e.b0=0; EMPTYL=internL(e); }
  El bl; bl.b0=0; bl.q=q0; BLANK=intern(bl); addG(BLANK);
  long RS= getenv("REAL")? atol(getenv("REAL")):0; if(RS>0) realRun(RS);
  emitTop("",0,0,BLANK);
  long it=0;
  while(!work.empty()){ int n=work.front(); work.pop_front(); inwork[n]=0; it++;
    if(nodes[n].kind) evaltop(n); else evalc(n);
    if(halted) break; if((long)nodes.size()>MAXN) break;
    if(it%2000000==0) fprintf(stderr,"it=%ld nodes=%zu (top %ld, contracts %ld) els=%zu classes=%zu work=%zu\n",it,nodes.size(),ntop,ncon,els.size(),cls.size(),work.size()); }
  size_t nsum=0; for(auto&v:Sum) nsum+=v.size(); long ng=0; for(char c:inG) ng+=c;
  const char*res= halted?"HALT-REACHABLE": ((long)nodes.size()>MAXN?"LIMIT": (gapfail?"GAP-UNBOUNDED":"NONHALT"));
  printf("%s %c R=%d cap=%d W=%d J=%d learn=%ld resk=%d : %s  classes=%zu exps=%zu G=%ld contracts=%ld facts=%zu top=%ld %s\n",m,argv[2][0],R,CAPL,Wn,J,LS,RESK,res,cls.size(),E.size(),ng,ncon,nsum,ntop,haltinfo.c_str());
  if(RS>0&&!getenv("NODIAG")){ DIAG=true; size_t nn=nodes.size(); long rt=0,rc=0; set<array<int,3>> rk; for(auto&m:realMicro) rk.insert({m[0],m[1],m[2]});
    for(size_t n=0;n<nn;n++){ if(nodes[n].kind){ if(realTop.count(topKey(nodes[n].x,nodes[n].h,nodes[n].s,nodes[n].a))) rt++; } else if(rk.count({nodes[n].l,nodes[n].s,nodes[n].a})){ rc++; halted=false; evalc(n); } }
    printf("real run: top configs %zu (%ld in the fixed point), calls %zu (%ld in the fixed point), facts %zu\n",realTop.size(),rt,rk.size(),rc,realFact.size()); }
  if(RS>0){ long sg=0; for(int a:gorder) if(!realG.count(a)) sg++;
    printf("real: G=%zu ; the fixed point has %ld G elements not seen in the real run\n",realG.size(),sg);
    }
  return 0;
}
