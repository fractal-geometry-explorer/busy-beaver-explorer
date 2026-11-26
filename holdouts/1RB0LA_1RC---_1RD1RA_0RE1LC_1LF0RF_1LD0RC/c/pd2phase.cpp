// Two-phase pushdown reachability. Phase A: the left side is abstracted by a token DFA DL, the right side is an exact
// stack (head cell on top). Phase B: the mirror (right side abstracted by DR, left side exact). Whenever the abstracted
// side's DFA state pins down its word exactly (few tokens), the configuration is handed to the other phase with the
// formerly exact side abstracted by the other DFA. Both reachable sets are computed by post* saturation, alternating
// until no new hand-over appears. Sound over-approximation of the run from blank tape: never halts if no halting
// transition is reachable in either phase and no DFA ever has to leave its learned language (escapes = 0).
// usage: pd2phase MACHINE n C LEARNSTEPS   (e.g. pd2phase 1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC 1 4 2000000)
// Result for this machine: no halting transition is reached in either phase and no concrete hand-over halts, but
// escapes remain (3381 at n=1 C=4): popping a token from the abstracted side rebuilds tapes the run never makes.
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
int Tw[6][2],Td[6][2],Tn[6][2];
const int INF=99, CAPA=12, CAPB=13;
int n,C; bool UNI=getenv("UNI")!=nullptr;

struct DFA {
  set<vector<int>> ALLOW;
  map<vector<int>,int> id; vector<vector<int>> W; vector<array<int,2>> d; vector<vector<pair<int,int>>> pre; int junk=-1;
  int get(const vector<int>&w){ auto it=id.find(w); if(it!=id.end()) return it->second; int k=W.size(); id[w]=k; W.push_back(w); d.push_back({-1,-1}); return k; }
  vector<int> step(const vector<int>&st,int x){
    if(st[0]<0) return st;
    int cnt=st[0],a=st[1],b=st[2];
    if(a==0){ if(x==0) return st; return {0,INF,1}; }
    vector<int> v=st;
    if(b==0){ if(x==0){ if(a+1>CAPA) return {-1}; v[1]=a+1; return v;} v[2]=1; return v; }
    if(x==1){ if(b+1>CAPB) return {-1}; v[2]=b+1; return v; }
    { vector<int> key={cnt,a,b}; if(!UNI) key.insert(key.end(),st.begin()+3,st.end()); if(!ALLOW.count(key)) return {-1}; }
    vector<int> h(st.begin()+3,st.end()); h.insert(h.begin(),b); h.insert(h.begin(),a); if(cnt+1>=C && (int)h.size()>2*n) h.resize(2*n);
    vector<int> r={min(cnt+1,C),1,0}; r.insert(r.end(),h.begin(),h.end()); return r;
  }
  void build(){ id.clear(); W.clear(); d.clear(); get({0,0,0});
    for(size_t i=0;i<W.size();i++) for(int a=0;a<2;a++){ auto v=step(W[i],a); d[i][a]=get(v); }
    auto it=id.find({-1}); junk= it==id.end()? -1: it->second;
    pre.assign(W.size(),{}); for(size_t p=0;p<W.size();p++) for(int a=0;a<2;a++) pre[d[p][a]].push_back({(int)p,a}); }
  // exact word (cells far -> near) if the state pins it down
  bool exact(int q, vector<int>&cells){ auto&v=W[q]; if(v[0]<0) return false; int cnt=v[0]; if(cnt>=C) return false;
    cells.clear(); if(v[1]==0) return true; // blank
    // completed tokens, oldest first: hist stored most recent first at v[3..]
    vector<pair<int,int>> toks; for(size_t i=3;i+1<v.size();i+=2) toks.push_back({v[i],v[i+1]}); reverse(toks.begin(),toks.end());
    toks.push_back({v[1],v[2]});
    for(auto&t:toks){ if(t.first!=INF) for(int k=0;k<t.first;k++) cells.push_back(0); for(int k=0;k<t.second;k++) cells.push_back(1); }
    return true; }
  string show(int q){ auto&v=W[q]; if(v[0]<0) return "JUNK"; string o="["+to_string(v[0])+": ("+to_string(v[1])+","+to_string(v[2])+") |"; for(size_t i=3;i+1<v.size();i+=2) o+=" ("+to_string(v[i])+","+to_string(v[i+1])+")"; return o+"]"; }
};

void learnTok(DFA&D,const string&m,long N,bool mir){
  int w[6][2],dd0[6][2],nx[6][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){ string x=m.substr(7*s+3*b,3); if(x[0]=='-'){nx[s][b]=-1;continue;} w[s][b]=x[0]-'0'; dd0[s][b]=(x[1]=='R')?1:-1; if(mir)dd0[s][b]=-dd0[s][b]; nx[s][b]=x[2]-'A'; }
  long TS=1<<24; vector<unsigned char> tp(TS,0); long p=TS/2,lo=p; int s=0;
  for(long i=0;i<N;i++){ int b=tp[p]; if(nx[s][b]<0) break; int wr=w[s][b]; tp[p]=wr; int dd=dd0[s][b]; s=nx[s][b];
    if(dd==1 && wr==0 && p-1>=lo && tp[p-1]==1){
      long q=p-1; int cntTok=0; vector<int> key;
      vector<int> tk;
      for(int k=0;k<=max(C,n)+1;k++){ int bb=0; while(q>=lo && tp[q]==1){bb++;q--;} int aa=0; while(q>=lo && tp[q]==0){aa++;q--;} if(q<lo) aa=INF;
        tk.push_back(min(aa,INF)); tk.push_back(bb); if(k>0) cntTok++; if(q<lo) break; }
      { int prev= cntTok<C? cntTok : min(n,cntTok); for(int k=0;k<=prev && 2*k+1<(int)tk.size();k++){ key.push_back(tk[2*k]); key.push_back(tk[2*k+1]); } }
      key.insert(key.begin(),min(cntTok,C)); if(UNI) key.resize(3); D.ALLOW.insert(key);
    }
    p+=dd; if(p<lo) lo=p; if(p<2||p>TS-3) break; }
}

const int BOT=2, EPS=3;
struct Phase {
  DFA*D; DFA*O; int dir; // dir=+1: phase A (machine as is), -1: mirrored
  int NC, F; int nstates;
  unordered_set<ll> rel; vector<vector<pair<int,int>>> out; vector<vector<int>> epsin; deque<array<int,3>> trans;
  map<pair<int,int>,int> midid; long esc=0; map<pair<int,int>,long> escs; set<pair<int,vector<int>>> inits;
  ll key(ll a,ll g,ll b){ return (a<<34)|(g<<32)|b; }
  void ensure(int q){ if((int)out.size()<=q){ out.resize(q+1); epsin.resize(q+1);} }
  void init(DFA*d_,DFA*o_,int dir_){ D=d_; O=o_; dir=dir_; NC=D->W.size()*6; F=NC; nstates=NC+1; ensure(F);
    isExact.assign(D->W.size(),0); vector<int> cl; for(size_t q=0;q<D->W.size();q++) isExact[q]=D->exact(q,cl); }
  int fresh(){ int k=nstates++; ensure(k); return k; }
  int mid(int c,int g){ auto k=make_pair(c,g); auto it=midid.find(k); if(it!=midid.end()) return it->second; int m=fresh(); midid[k]=m; return m; }
  bool addInit(int c,const vector<int>&stack){ // stack top first, without BOT
    if(!inits.insert({c,stack}).second) return false;
    int cur=c; for(size_t i=0;i<stack.size();i++){ int nx=fresh(); if(cur==c) trans.push_back({cur,stack[i],nx}); else { rel.insert(key(cur,stack[i],nx)); out[cur].push_back({stack[i],nx}); } cur=nx; }
    if(cur==c) trans.push_back({c,BOT,F}); else { rel.insert(key(cur,BOT,F)); out[cur].push_back({BOT,F}); }
    return true; }
  vector<char> isExact;
  void rules(int c,int g,vector<pair<int,vector<int>>>&R){ R.clear(); int q=c/6,s=c%6;
    if(isExact[q]) return; // cut: handed over
    if(g==BOT){ R.push_back({c,{0,BOT}}); return; }
    if(Tn[s][g]<0) return; int w=Tw[s][g], d=Td[s][g]*dir, s2=Tn[s][g];
    if(d==1){ int q2=D->d[q][w]; if(q2==D->junk){ esc++; escs[{q,s*2+w}]++; return; } R.push_back({q2*6+s2,{}}); }
    else for(auto&pa:D->pre[q]) R.push_back({pa.first*6+s2,{pa.second,w}}); }
  void saturate(){ vector<pair<int,vector<int>>> R;
    while(!trans.empty()){ auto t=trans.front(); trans.pop_front(); int p=t[0],g=t[1],q=t[2];
      ll k=key(p,g,q); if(rel.count(k)) continue; rel.insert(k); ensure(max(p,q));
      if(g!=EPS){ out[p].push_back({g,q});
        if(p<NC){ rules(p,g,R);
          for(auto&r:R){ int p2=r.first; auto&w=r.second;
            if(w.size()==0) trans.push_back({p2,EPS,q});
            else if(w.size()==1) trans.push_back({p2,w[0],q});
            else { int qm=mid(p2,w[0]); trans.push_back({p2,w[0],qm});
              ll k2=key(qm,w[1],q); if(!rel.count(k2)){ rel.insert(k2); out[qm].push_back({w[1],q}); for(int p3:epsin[qm]) trans.push_back({p3,w[1],q}); } } } }
      } else { epsin[q].push_back(p); for(auto&gq:out[q]) trans.push_back({p,gq.first,gq.second}); } } }
  int halting(int verbose){ int bad=0; for(int c=0;c<NC && c<(int)out.size();c++){ int s=c%6; if(isExact[c/6]) continue; for(auto&gq:out[c]){ int b= gq.first==BOT?0:gq.first; if(gq.first<=BOT && Tn[s][b]<0){ bad++; if(bad<=verbose) fprintf(stderr,"  HALT: D %s state %c reading %d\n",D->show(c/6).c_str(),'A'+s,b);} } } return bad; }
  // hand-overs: for controls with exact D state: (s, head cell h, O-state of the rest, exact word)
  void emissions(vector<tuple<int,int,int,vector<int>>>&em){ em.clear();
    // backward pairs (automaton state, O state) over non-P states
    vector<vector<array<int,2>>> rin(nstates); // rin[a] = (a', g) with transition a' -g-> a, g in {0,1}
    vector<int> botsrc;
    for(int a=0;a<(int)out.size();a++) for(auto&gq:out[a]){ if(gq.first==BOT && gq.second==F) botsrc.push_back(a); else if(gq.first<2) rin[gq.second].push_back({a,gq.first}); }
    set<pair<int,int>> seen; deque<pair<int,int>> dq; set<tuple<int,int,int>> emitted;
    auto push=[&](int a,int dO){ if(seen.insert({a,dO}).second) dq.push_back({a,dO}); };
    for(int a:botsrc){ if(a<NC){ emitted.insert({a,0,0}); } else push(a,0); }
    while(!dq.empty()){ auto [a,dO]=dq.front(); dq.pop_front();
      for(auto&e:rin[a]){ int a2=e[0], g=e[1];
        if(a2<NC){ emitted.insert({a2,g,dO}); }
        else { int d2=O->d[dO][g]; push(a2,d2); } } }
    vector<int> cells;
    for(auto&t:emitted){ auto [c,h,dO]=t; if(!D->exact(c/6,cells)) continue; em.push_back({c%6,h,dO,cells}); }
  }
};

int main(int argc,char**argv){
  string m=argv[1]; n=atoi(argv[2]); C=atoi(argv[3]); long LN=atol(argv[4]);
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){ string x=m.substr(7*s+3*b,3); if(x[0]=='-'){Tn[s][b]=-1;continue;} Tw[s][b]=x[0]-'0'; Td[s][b]=(x[1]=='R')?1:-1; Tn[s][b]=x[2]-'A'; }
  DFA DL,DR; learnTok(DL,m,LN,false); learnTok(DR,m,LN,true); DL.build(); DR.build();
  fprintf(stderr,"DL %zu states (%zu grams), DR %zu states (%zu grams)\n",DL.W.size(),DL.ALLOW.size(),DR.W.size(),DR.ALLOW.size());
  Phase A,B; A.init(&DL,&DR,1); B.init(&DR,&DL,-1);
  // concrete configurations: (state, left cells far->near, right cells near->far) with both sides exact
  set<tuple<int,vector<int>,vector<int>>> cseen; deque<tuple<int,vector<int>,vector<int>>> cq; long chalt=0, cesc=0;
  cq.push_back({0,{},{}}); cseen.insert({0,{},{}});
  auto runD=[&](DFA&D,const vector<int>&farToNear){ int q=0; for(int x:farToNear) q=D.d[q][x]; return q; };
  auto trimFar=[&](vector<int>&v,bool farIsFront){ if(farIsFront){ size_t k=0; while(k<v.size()&&v[k]==0) k++; v.erase(v.begin(),v.begin()+k);} else { while(!v.empty()&&v.back()==0) v.pop_back(); } };
  int MAXIT=atoi(getenv("MAXIT")?getenv("MAXIT"):"200");
  for(int it=0;it<MAXIT;it++){
    int added=0;
    // concrete runs
    while(!cq.empty()){ auto [s,L,R]=cq.front(); cq.pop_front();
      for(int step=0;step<100000;step++){
        int b= R.empty()?0:R[0];
        if(Tn[s][b]<0){ chalt++; fprintf(stderr,"  CONCRETE HALT\n"); break; }
        int w=Tw[s][b], d=Td[s][b];
        if(R.empty()) R.push_back(0); R[0]=w;
        if(d==1){ L.push_back(R[0]); R.erase(R.begin()); } else { int a= L.empty()?0:L.back(); if(!L.empty()) L.pop_back(); R.insert(R.begin(),a); }
        s=Tn[s][b]; trimFar(L,true); trimFar(R,false);
        vector<int> Rr(R.rbegin(),R.rend()); // far->near
        // DR reads the right side excluding the head cell, far->near
        vector<int> Rx; if(R.size()>1){ Rx.assign(R.rbegin(),R.rend()-1); }
        vector<int> Lx; if(!L.empty()) Lx.assign(L.begin(),L.end()-1);
        int qL=runD(DL,L), qR=runD(DR,Rx);
        if(qL==DL.junk || qR==DR.junk){ cesc++; if(cesc<=5){ fprintf(stderr,"  CESC state %c L=",(char)(65+s)); for(int x:L) fputc(48+x,stderr); fprintf(stderr," R="); for(int x:R) fputc(48+x,stderr); fprintf(stderr," junk %s\n", qL==DL.junk?"left":"right"); } break; }
        vector<int> cl;
        if(!DL.exact(qL,cl)){ // to A: control (qL, s), stack = R
          vector<int> st=R; if(st.empty()) st.push_back(0); while(st.size()>1&&st.back()==0) st.pop_back(); if(A.addInit(qL*6+s,st)) added++; break; }
        // phase B: control (D_R of right without head cell, s), stack = head cell then left nearest first
        if(!DR.exact(qR,cl)){ vector<int> st={R.empty()?0:R[0]}; for(int k=L.size()-1;k>=0;k--) st.push_back(L[k]); while(st.size()>1&&st.back()==0) st.pop_back(); if(B.addInit(qR*6+s,st)) added++; break; }
        if(!cseen.insert({s,L,R}).second) break;
      } }
    A.saturate(); B.saturate();
    vector<tuple<int,int,int,vector<int>>> em;
    // from A (left exact word cells far->near, head h, right-rest O state): if O state exact -> concrete, else -> B
    A.emissions(em); for(auto&e:em){ auto [s,h,dO,cells]=e; if(dO==DR.junk){ A.esc++; continue; } vector<int> cl;
      if(DR.exact(dO,cl)){ vector<int> R={h}; for(int k=cl.size()-1;k>=0;k--) R.push_back(cl[k]); while(!R.empty()&&R.back()==0) R.pop_back(); vector<int> L=cells; trimFar(L,true); if(cseen.insert({s,L,R}).second){ cq.push_back({s,L,R}); added++; } }
      else { vector<int> st={h}; for(int k=cells.size()-1;k>=0;k--) st.push_back(cells[k]); while(st.size()>1 && st.back()==0) st.pop_back(); if(B.addInit(dO*6+s,st)) added++; } }
    // from B: cells = right word far->near (excluding head), h head, dO = DL state of left rest
    B.emissions(em); for(auto&e:em){ auto [s,h,dO,cells]=e; if(dO==DL.junk){ B.esc++; continue; } vector<int> cl;
      if(DL.exact(dO,cl)){ vector<int> L=cl; trimFar(L,true); vector<int> R={h}; for(int k=cells.size()-1;k>=0;k--) R.push_back(cells[k]); while(!R.empty()&&R.back()==0) R.pop_back(); if(cseen.insert({s,L,R}).second){ cq.push_back({s,L,R}); added++; } }
      else { vector<int> st={h}; for(int k=cells.size()-1;k>=0;k--) st.push_back(cells[k]); while(st.size()>1 && st.back()==0) st.pop_back(); if(A.addInit(dO*6+s,st)) added++; } }
    fprintf(stderr,"iter %d: A rel %zu inits %zu esc %ld | B rel %zu inits %zu esc %ld | concrete %zu halt %ld esc %ld | new %d\n",it,A.rel.size(),A.inits.size(),A.esc,B.rel.size(),B.inits.size(),B.esc,cseen.size(),chalt,cesc,added);
    if(!added && cq.empty()) break;
  }
  int ha=A.halting(5), hb=B.halting(5);
  for(auto*P:{&A,&B}){ int k=0; for(auto&e:P->escs) if(k++<10) fprintf(stderr,"  ESC phase %c: D %s state %c writes %d\n",P==&A?'A':'B',P->D->show(e.first.first).c_str(),'A'+e.first.second/2,e.first.second%2); }
  printf("concrete halts %ld esc %ld  n %d C %d  A: rel %zu halting %d esc %ld  B: rel %zu halting %d esc %ld\n",chalt,cesc,n,C,A.rel.size(),ha,A.esc,B.rel.size(),hb,B.esc);
}
