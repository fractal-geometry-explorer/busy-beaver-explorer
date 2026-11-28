// tokgram: call-summary decider over run tokens, with half tapes named by the call that produced them.
//
// The machine is mirrored if needed so that the regular end of the tape is the left end.
// Tokens are maximal runs of equal cells. A run length is kept exactly below CAP and as ">= CAP with known
// parity" from CAP on. A half tape (the cells right of some boundary, nearest first) is described by a few
// explicit runs followed by a nonterminal of a right-linear grammar over runs (N -> run N').
// A call (ctx, s, a) is the head in state s on the first cell of half tape a, with a left context ctx (at most
// J runs, nearest first). It returns when the head leaves ctx to the left; its summary is the set of
// (return state, half tape right of the left edge of ctx). A returned half tape with more than R explicit runs
// is cut after R runs and the rest gets a nonterminal named by the call (context, state, explicit runs, the
// call's own nonterminal truncated to nesting depth j), the return state and the R runs (as in
// ../return-shape/sba.py). The top level keeps the first W cells from the leftmost 1 exactly.
// The analysis starts from the real configuration after T0 steps (first time after T0 that the head is inside
// the exact part). Least fixed point; if no halting transition is reachable in it, the machine does not halt
// from that configuration, hence (having run T0 steps without halting) not at all.
//
// Usage: [J=runs] [DEPTH=j] [T0=steps] [SEEDMAX=steps] [TL=seconds] [CERT=file] tokgram MACHINE L|R R CAP W [MAXNODES]
#include <bits/stdc++.h>
using namespace std;
static int Wr[6][2],Dr[6][2],NX[6][2];
static int R=2, CAPL=4, J=2, DEPTH=1, Wn=8;
static inline uint8_t code(long L){ return L<CAPL? L : CAPL+(L&1); }
static inline uint8_t incLen(uint8_t L){ if(L<CAPL-1) return L+1; if(L==CAPL-1) return CAPL+(CAPL&1); return CAPL+((L-CAPL)^1); }
static string runsStr(int b0,const vector<uint8_t>&len){ string r; int bit=b0; for(size_t i=0;i<len.size();i++){ if(i) r+=' '; r+=to_string(bit); r+='^'; if(len[i]<CAPL) r+=to_string(len[i]); else r+=string(len[i]-CAPL?"odd":"even")+">="+to_string(CAPL); bit^=1; } return r; }
// ---------- nonterminals ----------
struct NT { int kind; string base, tail; int inner; int k; string name; }; // kind 0 END, 1 STAR, 2 SEED, 3 O/X (base, inner, tail), 4 T (inner, k)
static vector<NT> nts; static unordered_map<string,int> ntmap;
static vector<vector<array<int,3>>> prods; static vector<set<array<int,3>>> prodset; static vector<vector<int>> ntdeps;
static int ntIntern(NT n){ auto it=ntmap.find(n.name); if(it!=ntmap.end()) return it->second; int id=nts.size(); nts.push_back(n); ntmap[n.name]=id; prods.emplace_back(); prodset.emplace_back(); ntdeps.emplace_back(); return id; }
static int END_,STAR_;
static int mkO(const string&base,int inner,const string&tail){ NT n; n.kind=3; n.base=base; n.tail=tail; n.inner=inner; n.k=0; n.name="O{"+base+"|"+nts[inner].name+"|"+tail+"}"; return ntIntern(n); }
static int mkT(int inner,int k){ NT n; n.kind=4; n.inner=inner; n.k=k; n.name="T{"+nts[inner].name+"#"+to_string(k)+"}"; return ntIntern(n); }
static int truncN(int id,int d){ NT n=nts[id]; if(n.kind==3){ if(d==0) return STAR_; return mkO(n.base,truncN(n.inner,d-1),n.tail); } if(n.kind==4) return mkT(truncN(n.inner,d),n.k); return id; }
// ---------- half tapes ----------
struct El { uint8_t b0; vector<uint8_t> len; int n; };
static vector<El> els; static unordered_map<string,int> elmap; static int BLANK=0;
static int intern(const El&e){ string k; k.push_back(e.len.empty()?0:e.b0); k.append(e.len.begin(),e.len.end()); k.push_back((char)255); k.append((const char*)&e.n,4);
  auto it=elmap.find(k); if(it!=elmap.end()) return it->second; int id=els.size(); els.push_back(e); if(e.len.empty()) els.back().b0=0; elmap[k]=id; return id; }
static string elstr(int a){ const El&e=els[a]; return "["+runsStr(e.b0,e.len)+" | "+(nts[e.n].name.size()>60? "N"+to_string(e.n) : nts[e.n].name)+"]"; }
static int Cons(int c,int a){ El e=els[a];
  if(e.len.empty()){ if(e.n!=END_){ fprintf(stderr,"internal: empty explicit part\n"); exit(3); } if(c==0) return a; e.b0=1; e.len={1}; return intern(e); }
  if(e.b0==c) e.len[0]=incLen(e.len[0]); else { e.len.insert(e.len.begin(),1); e.b0=c; } return intern(e); }
struct Node { int kind; int s,a,l; string x; int h; };  // kind 0 = call (l,s,a), 1 = top config
static vector<Node> nodes; static unordered_map<string,int> nodemap;
static vector<set<pair<int,int>>> Sum; static vector<vector<int>> deps;
static deque<int> work; static vector<char> inwork; static long ntop=0,ncon=0,nprod=0;
static void push(int n){ if(!inwork[n]){ inwork[n]=1; work.push_back(n); } }
static void addProd(int N,int bit,int cd,int N2){ if(prodset[N].insert({bit,cd,N2}).second){ prods[N].push_back({bit,cd,N2}); nprod++; for(int u:ntdeps[N]) push(u); } }
// remove the first cell of a; returns the possible rests
static void unfold(int a,int user,vector<int>&out){ out.clear(); El e=els[a];
  if(e.len.empty()){ out.push_back(a); return; }
  uint8_t L=e.len[0]; int c=e.b0;
  if(L>=CAPL){ int par=L-CAPL; El f=e; f.len[0]=CAPL+(par^1); out.push_back(intern(f)); if(((CAPL-1)&1)==(par^1)) L=CAPL; else return; }
  if(L>1){ e.len[0]=L-1; out.push_back(intern(e)); return; }
  e.len.erase(e.len.begin()); e.b0=c^1;
  if(!e.len.empty()){ out.push_back(intern(e)); return; }
  int N=e.n; if(N==END_){ out.push_back(BLANK); return; }
  auto&v=ntdeps[N]; if(find(v.begin(),v.end(),user)==v.end()) v.push_back(user);
  for(auto&p:prods[N]){ if(p[0]==c){ fprintf(stderr,"internal: run not maximal at %s\n",nts[N].name.c_str()); exit(3); } El f; f.b0=p[0]; f.len={(uint8_t)p[1]}; f.n=p[2]; out.push_back(intern(f)); } }
// cut a half tape after R runs, naming the rest
static int normalise(int a,const string&base,int inner,const string&tailPrefix){ const El&e0=els[a]; if((int)e0.len.size()<=R) return a; El e=e0;
  vector<uint8_t> head(e.len.begin(),e.len.begin()+R);
  int N=mkO(base,inner,tailPrefix+runsStr(e.b0,head)); int cur=N; int n=e.len.size();
  for(int i=R;i<n;i++){ int nx= i==n-1? e.n : mkT(N,i-R+1); addProd(cur,e.b0^(i&1),e.len[i],nx); cur=nx; }
  El f; f.b0=e.b0; f.len=head; f.n=N; return intern(f); }
// ---------- left contexts ----------
struct Lc { uint8_t b0; vector<uint8_t> len; };
static vector<Lc> lcs; static unordered_map<string,int> lcmap; static int EMPTYL=0;
static int internL(const Lc&e){ string k; k.push_back(e.len.empty()?0:e.b0); k.append(e.len.begin(),e.len.end());
  auto it=lcmap.find(k); if(it!=lcmap.end()) return it->second; int id=lcs.size(); lcs.push_back(e); if(e.len.empty()) lcs.back().b0=0; lcmap[k]=id; return id; }
static int pushL(int l,int c){ Lc e=lcs[l]; if(!e.len.empty()&&e.b0==c) e.len[0]=incLen(e.len[0]); else { e.len.insert(e.len.begin(),1); e.b0=c; } return internL(e); }
static void popL(int l,vector<int>&out){ Lc e=lcs[l]; uint8_t L=e.len[0];
  if(L>=CAPL){ int par=L-CAPL; Lc f=e; f.len[0]=CAPL+(par^1); out.push_back(internL(f)); if(((CAPL-1)&1)==(par^1)){ L=CAPL; } else return; }
  if(L>1){ e.len[0]=L-1; out.push_back(internL(e)); } else { e.len.erase(e.len.begin()); e.b0^=1; out.push_back(internL(e)); } }
static string lcstr(int l){ return "<"+runsStr(lcs[l].b0,lcs[l].len)+">"; }
// ---------- fixed point ----------
static bool halted=false; static string haltinfo; static long SEEDSTEP=0;
static int nodeId(const Node&nd){ string k; k.push_back('0'+nd.kind); k.push_back('A'+nd.s); k.append((const char*)&nd.a,4); k.append((const char*)&nd.l,4); if(nd.kind){ k.append((const char*)&nd.h,4); k+=nd.x; }
  auto it=nodemap.find(k); if(it!=nodemap.end()) return it->second; int id=nodes.size(); nodes.push_back(nd); nodemap[k]=id; Sum.emplace_back(); deps.emplace_back(); inwork.push_back(0);
  if(nd.kind) ntop++; else ncon++; push(id); return id; }
static int contract(int l,int s,int a){ Node nd; nd.kind=0; nd.s=s; nd.a=a; nd.h=0; nd.l=l; return nodeId(nd); }
static void adddep(int c,int n){ auto&v=deps[c]; if(find(v.begin(),v.end(),n)==v.end()) v.push_back(n); }
static void evalc(int id){ int s=nodes[id].s, a=nodes[id].a, l0=nodes[id].l;
  string base=lcstr(l0)+string(1,'A'+s)+runsStr(els[a].b0,els[a].len); int inner=truncN(els[a].n,DEPTH);
  set<tuple<int,int,int>> seen; vector<tuple<int,int,int>> st;
  map<tuple<int,int,int>,pair<tuple<int,int,int>,string>> par; tuple<int,int,int> curm; string note; bool TR=getenv("TRACE")!=0;
  auto add=[&](int l,int q,int b){ auto m=make_tuple(l,q,b); if(seen.insert(m).second){ st.push_back(m); if(TR) par[m]={curm,note}; } };
  bool changed=false;
  auto landLeft=[&](int l,int q,int b){
    if(lcs[l].len.empty()){ int r=normalise(b,base,inner,string(1,'A'+q)); if(Sum[id].insert({q,r}).second){ changed=true;
        if(TR&&getenv("TF")){ string me=lcstr(l0)+" "+string(1,'A'+s)+" "+elstr(a)+" -> "+string(1,'A'+q)+" "+elstr(r); if(me.find(getenv("TF"))==0){ printf("FACT %s  (before cut: %s) [%s]\n",me.c_str(),elstr(b).c_str(),note.c_str());
          vector<string> lines; auto m=curm; while(par.count(m)){ auto [l_,q_,b_]=m; lines.push_back("  "+lcstr(l_)+" "+string(1,'A'+q_)+" "+elstr(b_)+"    "+par[m].second); m=par[m].first; if(m==make_tuple(-1,-1,-1)) break; } for(int i=lines.size()-1;i>=0;i--) puts(lines[i].c_str()); } } } return; }
    int x=lcs[l].b0; vector<int> ls; popL(l,ls); int b2=Cons(x,b); for(int l2:ls) add(l2,q,b2); };
  curm=make_tuple(-1,-1,-1); add(l0,s,a); vector<int> iv;
  while(!st.empty()){ auto [l,q,b]=st.back(); st.pop_back(); curm=make_tuple(l,q,b);
    int c1= els[b].len.empty()?0:els[b].b0; unfold(b,id,iv); vector<int> rests=iv;
    if(NX[q][c1]<0){ if(rests.empty()) continue; halted=true;
      if(TR){ vector<string> lines; auto m=curm; while(par.count(m)){ auto [l_,q_,b_]=m; lines.push_back("  "+lcstr(l_)+" "+string(1,'A'+q_)+" "+elstr(b_)+"    "+par[m].second); m=par[m].first; if(m==make_tuple(-1,-1,-1)) break; } for(int i=lines.size()-1;i>=0;i--) puts(lines[i].c_str()); } haltinfo="call "+lcstr(l0)+" "+string(1,'A'+s)+" "+elstr(a)+" at "+lcstr(l)+" "+string(1,'A'+q)+" "+elstr(b); return; }
    int w=Wr[q][c1], d=Dr[q][c1], q2=NX[q][c1];
    for(int b1:rests){
      if(d<0) landLeft(l,q2,Cons(w,b1));
      else { int l2=pushL(l,w);
        if((int)lcs[l2].len.size()<=J) add(l2,q2,b1);
        else { Lc in=lcs[l2]; Lc out; out.b0=in.b0^(J&1); out.len.assign(in.len.begin()+J,in.len.end()); in.len.resize(J); int lin=internL(in), lout=internL(out);
          int cc=contract(lin,q2,b1); adddep(cc,id);
          vector<pair<int,int>> tmp(Sum[cc].begin(),Sum[cc].end()); for(auto&pr:tmp){ if(TR) note="after nested call "+lcstr(lin)+" "+string(1,'A'+q2)+" "+elstr(b1)+" returned "+string(1,'A'+pr.first)+" "+elstr(pr.second); landLeft(lout,pr.first,pr.second); } note.clear(); } } } }
  if(changed){ vector<int> dv=deps[id]; for(int d_:dv) push(d_); }
}
static bool gapfail=false;
static void emitTop(string x,int h,int s,int a){
  if(x.empty()&&a==BLANK) h=0;
  if(a==BLANK){ while(!x.empty()&&x.back()=='0') x.pop_back(); }
  if((int)els[a].len.size()>R+4){ a=normalise(a,"X",truncN(els[a].n,DEPTH),""); }
  Node nd; nd.kind=1; nd.s=s; nd.a=a; nd.x=x; nd.h=h; nd.l=0; nodeId(nd); }
static void evaltop(int id){ Node nd=nodes[id]; string x=nd.x; int h=nd.h, s=nd.s, a=nd.a; int len=x.size();
  int c = (h>=0&&h<len)? x[h]-'0' : 0;
  if(NX[s][c]<0){ halted=true; haltinfo="top x="+x+" h="+to_string(h)+" state "+string(1,'A'+s)+" a="+elstr(a); return; }
  int w=Wr[s][c], d=Dr[s][c], s2=NX[s][c];
  vector<pair<string,pair<int,int>>> cands; vector<int> iv;
  if(h>=0&&h<len){ x[h]='0'+w;
    if(x[0]=='0'){ size_t z=x.find('1'); if(z!=string::npos){ x=x.substr(z); h-=z; cands.push_back({x,{h,a}}); }
      else { int zeros=len; h-=zeros; set<pair<int,int>> seen; vector<pair<int,int>> st; st.push_back({a,0}); seen.insert({a,0});
        while(!st.empty()){ auto [b,z2]=st.back(); st.pop_back();
          if(b==BLANK){ cands.push_back({"",{0,BLANK}}); continue; }
          if(z2>4*Wn+64){ gapfail=true; continue; }
          int cb=els[b].b0; unfold(b,id,iv); vector<int> rests=iv;
          for(int b1:rests){ if(cb==1) cands.push_back({"1",{h-z2,b1}}); else if(seen.insert({b1,z2+1}).second) st.push_back({b1,z2+1}); } } } }
    else cands.push_back({x,{h,a}}); }
  else if(h<0){ if(w==1){ x=string("1")+string(-h-1,'0')+x; h=0; } cands.push_back({x,{h,a}}); }
  else { if(w==1){ x="1"; h=0; } cands.push_back({x,{h,a}}); }
  for(auto&cd:cands){ string y=cd.first; int hh=cd.second.first; int b=cd.second.second;
    while((int)y.size()>Wn){ int cc=y.back()-'0'; y.pop_back(); b=Cons(cc,b); }
    int ylen=y.size();
    if(ylen==0){ emitTop(y,0,s2,b); continue; }
    int nh=hh+d;
    if(nh<ylen){ emitTop(y,nh,s2,b); continue; }
    if((int)els[b].len.size()>R+4) b=normalise(b,"X",truncN(els[b].n,DEPTH),"");
    int cc=contract(EMPTYL,s2,b); adddep(cc,id);
    vector<pair<int,int>> tmp(Sum[cc].begin(),Sum[cc].end()); for(auto&pr:tmp) emitTop(y,ylen-1,pr.first,pr.second); }
}
int main(int argc,char**argv){
  if(argc<6){ fprintf(stderr,"usage: [J=] [DEPTH=] [T0=] tokgram MACHINE L|R R CAP W [MAXNODES]\n"); return 1; }
  char*m=argv[1]; bool mirror=argv[2][0]=='R'; R=atoi(argv[3]); CAPL=atoi(argv[4]); Wn=atoi(argv[5]); long MAXN= argc>6? atol(argv[6]):3000000;
  if(getenv("J")) J=atoi(getenv("J")); if(getenv("DEPTH")) DEPTH=atoi(getenv("DEPTH")); long T0= getenv("T0")? atol(getenv("T0")):0; double TL= getenv("TL")? atof(getenv("TL")):1e9; long SEEDMAX= getenv("SEEDMAX")? atol(getenv("SEEDMAX")):2000000000L;
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*x=m+7*s+3*b; if(x[0]=='-'){NX[s][b]=-1;continue;} Wr[s][b]=x[0]-'0'; Dr[s][b]=x[1]=='R'?1:-1; if(mirror)Dr[s][b]=-Dr[s][b]; NX[s][b]=x[2]-'A';}
  { NT n; n.kind=0; n.inner=0; n.k=0; n.name="$"; END_=ntIntern(n); n.kind=1; n.name="*"; STAR_=ntIntern(n); }
  { Lc e; e.b0=0; EMPTYL=internL(e); } { El bl; bl.b0=0; bl.n=END_; BLANK=intern(bl); }
  // seed configuration
  { long T=1L<<26; vector<uint8_t> tape(T,0); long p=T/2; int s=0; long lo=p,hi=p; long i=0; bool ok=false; long E=0;
    for(;;i++){ if(i>=T0){ E=lo; while(E<=hi&&tape[E]==0) E++; if(E>hi){ ok=true; break; } if(p>=E-Wn&&p<E+Wn){ long last=hi; while(tape[last]==0) last--; if(p<= min(last,E+Wn-1)) { ok=true; break; } } }
      int b=tape[p]; if(NX[s][b]<0){ printf("%s halts in the seed run at step %ld\n",m,i); return 0; } tape[p]=Wr[s][b]; int d=Dr[s][b]; s=NX[s][b]; p+=d; if(p<lo)lo=p; if(p>hi)hi=p; if(i>T0+SEEDMAX||p<8||p>T-8) break; }
    if(!ok){ printf("no seed configuration found\n"); return 0; }
    fprintf(stderr,"seed at step %ld\n",i); SEEDSTEP=i;
    if(E>hi) emitTop("",0,s,BLANK);
    else { long last=hi; while(tape[last]==0) last--; string x; long j=E; for(;j<=last&&(int)x.size()<Wn;j++) x.push_back('0'+tape[j]);
      vector<pair<int,long>> runs; for(long k=j;k<=last;){ long k2=k; while(k2<=last&&tape[k2]==tape[k]) k2++; runs.push_back({tape[k],k2-k}); k=k2; }
      El e; e.b0= runs.empty()?0:runs[0].first; e.n=END_; int n=runs.size();
      if(n>R){ int cur=-1; for(int k=R;k<n;k++){ NT t; t.kind=2; t.inner=0; t.k=k; t.name="S"+to_string(k); int N=ntIntern(t); if(k==R) e.n=N; else addProd(cur,runs[k-1].first,code(runs[k-1].second),N); cur=N; } addProd(cur,runs[n-1].first,code(runs[n-1].second),END_); }
      for(int k=0;k<n&&k<R;k++) e.len.push_back(code(runs[k].second));
      emitTop(x,(int)(p-E),s,intern(e)); } }
  long it=0; clock_t t0=clock();
  while(!work.empty()){ int n=work.front(); work.pop_front(); inwork[n]=0; it++;
    if(nodes[n].kind) evaltop(n); else evalc(n);
    if(halted) break; if((long)nodes.size()>MAXN||(long)nts.size()>MAXN) break; if((it&1023)==0&&(double)(clock()-t0)/CLOCKS_PER_SEC>TL) break; }
  size_t nsum=0; for(auto&v:Sum) nsum+=v.size();
  const char*res= halted?"HALT-REACHABLE": (!work.empty()?"LIMIT": (gapfail?"GAP-UNBOUNDED":"NONHALT"));
  printf("%s %c R=%d cap=%d W=%d J=%d depth=%d T0=%ld : %s  nonterminals=%zu productions=%ld calls=%ld facts=%zu top=%ld evals=%ld %.1fs %s\n",m,argv[2][0],R,CAPL,Wn,J,DEPTH,T0,res,nts.size(),nprod,ncon,nsum,ntop,it,(double)(clock()-t0)/CLOCKS_PER_SEC,haltinfo.substr(0,300).c_str());
  if(getenv("CERT")&&!halted&&work.empty()&&!gapfail){ FILE*f=fopen(getenv("CERT"),"w");
    fprintf(f,"tokgram-certificate 1\nmachine %s\nmirror %d\ncap %d\nwindow %d\ncontext %d\nseedstep %ld\n",m,(int)mirror,CAPL,Wn,J,SEEDSTEP);
    auto runs=[&](int b0,const vector<uint8_t>&len){ string r=to_string(len.empty()?0:b0); for(auto L:len){ r+=' '; r+=to_string((int)L); } return r; };
    for(size_t n=0;n<nts.size();n++){ if(prods[n].empty()&&(int)n!=END_) continue; fprintf(f,"N %zu%s :",n,(int)n==END_?" end":""); for(auto&p:prods[n]) fprintf(f," %d %d %d",p[0],p[1],p[2]); fprintf(f,"\n"); }
    for(size_t n=0;n<nodes.size();n++){ const Node&nd=nodes[n]; const El&e=els[nd.a];
      if(nd.kind) fprintf(f,"T %s %d %c ; %s ; %d\n",nd.x.empty()?"-":nd.x.c_str(),nd.h,'A'+nd.s,runs(e.b0,e.len).c_str(),e.n);
      else { fprintf(f,"C %s ; %c ; %s ; %d :",runs(lcs[nd.l].b0,lcs[nd.l].len).c_str(),'A'+nd.s,runs(e.b0,e.len).c_str(),e.n);
        for(auto&pr:Sum[n]){ const El&r=els[pr.second]; fprintf(f," %c ; %s ; %d /",'A'+pr.first,runs(r.b0,r.len).c_str(),r.n); } fprintf(f,"\n"); } }
    fclose(f); }
  return 0;
}
