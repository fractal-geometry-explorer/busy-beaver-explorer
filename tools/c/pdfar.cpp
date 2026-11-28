// One-sided finite automata reduction with an exact side: the tape left of the head is abstracted by a DFA D read
// from the far left (here: the window of the last K cells, '#' = blank from here on), the tape right of the head is
// kept exactly, as the stack of a pushdown system whose control states are (D state, machine state).  A right move
// pops the head cell and steps D; a left move replaces the head cell by (a, written) for every D predecessor (p, a)
// of the current D state.  The blank right end is a bottom symbol that expands to 0.  The forward reachable set of
// this pushdown system is regular and computed exactly by post* saturation (Schwoon 2002, Algorithm 2); it contains
// every configuration of the real run from blank tape.  If no reachable control state can read a symbol whose
// transition halts, the machine never halts.  `mirror` swaps the roles of the sides.
// Checked on the 53 holdouts the repository has proved halting (none is claimed); on the 608 holdouts of
// BB6_holdouts_608.txt it decides none for K <= 10 on either side (26 November 2026).
// usage: pdfar MACHINE K [mirror]      prints "... halting H": H = 0 means never halts
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
int Tw[6][2],Td[6][2],Tn[6][2];
int K;
// ---- DFA D: windows far->near, letters 0,1,2(#)
map<vector<int>,int> Did; vector<vector<int>> Dw; vector<array<int,2>> Dd;
int dget(const vector<int>&w){ auto it=Did.find(w); if(it!=Did.end()) return it->second; int id=Dw.size(); Did[w]=id; Dw.push_back(w); Dd.push_back({-1,-1}); return id; }
void buildD(){
  vector<int> b(K,2); dget(b);
  for(size_t i=0;i<Dw.size();i++) for(int a=0;a<2;a++){
    vector<int> w=Dw[i]; int dropped=w[0]; vector<int> v(w.begin()+1,w.end()); v.push_back(a);
    if(dropped==2){ for(int j=0;j<K && v[j]==0;j++) v[j]=2; }
    Dd[i][a]=dget(v); }
}
int main(int argc,char**argv){
  string m=argv[1]; K=atoi(argv[2]); bool mir=argc>3;
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){ string x=m.substr(7*s+3*b,3); if(x[0]=='-'){Tn[s][b]=-1;continue;} Tw[s][b]=x[0]-'0'; Td[s][b]=(x[1]=='R')?1:-1; if(mir) Td[s][b]=-Td[s][b]; Tn[s][b]=x[2]-'A'; }
  buildD(); int nD=Dw.size();
  vector<vector<pair<int,int>>> Dpre(nD); // (p,a) with d(p,a)=q
  for(int p=0;p<nD;p++) for(int a=0;a<2;a++) Dpre[Dd[p][a]].push_back({p,a});
  fprintf(stderr,"D states %d\n",nD);
  // control states: c = q*6+s ; automaton states: controls [0,NC), f = NC, then mid states q_{p',g}
  int NC=nD*6; int F=NC;
  const int BOT=2, EPS=3;
  // rules: from (c,g) -> list of (c', w) with w length 0..2 (encoded vector)
  // generate on the fly
  map<pair<int,int>,int> midid; vector<pair<int,int>> mids;
  auto mid=[&](int c,int g){ auto k=make_pair(c,g); auto it=midid.find(k); if(it!=midid.end()) return it->second; int id=NC+1+mids.size(); midid[k]=id; mids.push_back(k); return id; };
  auto rules=[&](int c,int g,vector<pair<int,vector<int>>>&out){ out.clear(); int q=c/6,s=c%6;
    if(g==BOT){ out.push_back({c,{0,BOT}}); return; }
    if(Tn[s][g]<0) return; int w=Tw[s][g], d=Td[s][g], s2=Tn[s][g];
    if(d==1){ out.push_back({Dd[q][w]*6+s2,{}}); }
    else for(auto&pa:Dpre[q]) out.push_back({pa.first*6+s2,{pa.second,w}});
  };
  auto key=[&](ll a,ll g,ll b){ return (a<<34)|(g<<32)|b; };
  unordered_set<ll> rel; vector<vector<pair<int,int>>> out; // out[q] = (g,to) non-eps
  vector<vector<int>> epsin; // epsin[q] = p with (p,eps,q)
  auto ensure=[&](int q){ if((int)out.size()<=q){ out.resize(q+1); epsin.resize(q+1);} };
  deque<array<int,3>> trans;
  int c0=0*6+0; // start: D state of the all-blank left side (index 0), machine state A
  trans.push_back({c0,BOT,F});
  vector<pair<int,vector<int>>> R; long iter=0;
  while(!trans.empty()){
    auto t=trans.front(); trans.pop_front(); int p=t[0],g=t[1],q=t[2];
    ll k=key(p,g,q); if(rel.count(k)) continue; rel.insert(k); ensure(max(p,q));
    if(++iter%5000000==0) fprintf(stderr,"rel %zu trans %zu mids %zu\n",rel.size(),trans.size(),mids.size());
    if(g!=EPS){
      out[p].push_back({g,q});
      if(p<NC){
        rules(p,g,R);
        for(auto&r:R){ int p2=r.first; auto&w=r.second;
          if(w.size()==0) trans.push_back({p2,EPS,q});
          else if(w.size()==1) trans.push_back({p2,w[0],q});
          else { int qm=mid(p2,w[0]); ensure(qm); trans.push_back({p2,w[0],qm});
            ll k2=key(qm,w[1],q); if(!rel.count(k2)){ rel.insert(k2); out[qm].push_back({w[1],q}); for(int p3:epsin[qm]) trans.push_back({p3,w[1],q}); }
          }
        }
      }
    } else {
      epsin[q].push_back(p);
      for(auto&gq:out[q]) trans.push_back({p,gq.first,gq.second});
    }
  }
  fprintf(stderr,"rel %zu mids %zu\n",rel.size(),mids.size());
  // halting check: control c with state s, symbol b halting, has a transition on b (non-eps out of c) -- eps already folded
  int bad=0; set<int> ctrl;
  for(int c=0;c<NC && c<(int)out.size();c++){ if(out[c].empty()) continue; ctrl.insert(c/6); int s=c%6;
    for(auto&gq:out[c]){ int g=gq.first; int b= g==BOT?0:g; if(Tn[s][b]<0){ bad++; if(bad<=10){ fprintf(stderr,"HALT reachable: D window "); for(int x:Dw[c/6]) fputc("01#"[x],stderr); fprintf(stderr," state %c reading %d (sym %d)\n",'A'+s,b,g);} } } }
  printf("K %d mirror %d Dstates %d used %zu rel %zu halting %d\n",K,(int)mir,nD,ctrl.size(),rel.size(),bad);
}
