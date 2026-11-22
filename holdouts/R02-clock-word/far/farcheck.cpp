// The same check as farsearch.c for one given left DFA (file: n, then n lines "succ0 succ1"; state 0 is the far
// left, with 0 -> 0 for the blank tape), by a worklist propagation that scales to thousands of DFA states.
// Prints CLOSED (an invariant: no halt from the start for any word) or HALT reachable (the abstraction allows a halt).
// Environment: LEFTPRE=cells puts those cells left of the head at the start; MIRROR=1 swaps left and right (the DFA
// then reads the word side; argv[5] = cells between the word and the head).
// usage: farcheck MACHINE STARTSTATE PREFIX DFAFILE [MIRRORPREFIX]   (dfa_window.py writes window DFAs)
#include <bits/stdc++.h>
using namespace std;
int tw[6][2],td[6][2],tt[6][2],th[6][2];
int n; vector<array<int,2>> D;
int NN; // nodes
vector<vector<int>> cl;           // Cl(X) members list
vector<unordered_set<int>> clset;
vector<vector<int>> epred;        // eps predecessors
vector<unordered_set<int>> eset;  // eps successors set (dedupe)
vector<vector<pair<int,int>>> lab; // labeled edges (b, y)
vector<int> isN; // for node X = N(q,f): q*6+f else -1
deque<pair<int,int>> wl;
int Nid(int q,int f){return q*6+f;}
int Bid(int q,int f,int b){return 6*n+(q*6+f)*2+b;}
int ACC;
void add(int X,int Z){ if(clset[X].insert(Z).second){cl[X].push_back(Z); wl.push_back({X,Z});} }
void addeps(int X,int Y){ if(!eset[X].insert(Y).second) return; epred[Y].push_back(X); for(size_t i=0;i<cl[Y].size();i++) add(X,cl[Y][i]); }
int main(int argc,char**argv){
  char*m=argv[1]; int q0s=argv[2][0]-'A'; vector<int> pre; for(char*p=argv[3];*p;p++) pre.push_back(*p-'0');
  FILE*F=fopen(argv[4],"r"); if(fscanf(F,"%d",&n)!=1)return 2; D.resize(n); for(int q=0;q<n;q++) if(fscanf(F,"%d %d",&D[q][0],&D[q][1])!=2) return 2; fclose(F);
  vector<pair<int,int>> lr;
  for(int f=0;f<6;f++)for(int b=0;b<2;b++){char*s=m+7*f+3*b; if(s[0]=='-'){th[f][b]=1;continue;} tw[f][b]=s[0]-'0'; td[f][b]=s[1]=='R'?1:-1; if(getenv("MIRROR")) td[f][b]=-td[f][b]; tt[f][b]=s[2]-'A'; if(td[f][b]<0) lr.push_back({f,b});}
  int nl=lr.size();
  int Abase=18*n; int Sbase=Abase+n*2*nl; int U=Sbase+pre.size()+1, Z=U+1; ACC=Z+1; NN=ACC+1;
  cl.resize(NN); clset.resize(NN); epred.resize(NN); eset.resize(NN); lab.resize(NN);
  for(int X=0;X<NN;X++) add(X,X);
  // labeled static edges
  for(int k=0;k<nl;k++){int f=lr[k].first,b=lr[k].second,w=tw[f][b],t=tt[f][b];
    for(int p=0;p<n;p++)for(int c=0;c<2;c++){int q=D[p][c]; int a=Abase+(p*2+c)*nl+k; lab[Nid(p,t)].push_back({c,a}); lab[a].push_back({w,Bid(q,f,b)});}}
  for(size_t i=0;i<pre.size();i++) lab[Sbase+i].push_back({pre[i],Sbase+i+1});
  lab[U].push_back({0,U}); lab[U].push_back({1,U}); lab[Z].push_back({0,Z});
  addeps(U,ACC); addeps(Z,ACC);
  if(getenv("MIRROR")){ // argv[5] = left prefix (cells, far first) after an arbitrary word; pre = head + right cells then blank
    vector<int> lp; for(char*p=argv[5];*p;p++) lp.push_back(*p-'0');
    vector<char> R(n,0); vector<int> stk={0}; R[0]=1; while(!stk.empty()){int q=stk.back();stk.pop_back(); for(int c=0;c<2;c++) if(!R[D[q][c]]){R[D[q][c]]=1;stk.push_back(D[q][c]);}}
    for(int p=0;p<n;p++) if(R[p]){ int q=p; for(int c:lp) q=D[q][c]; addeps(Nid(q,q0s),Sbase);} 
    addeps(Sbase+pre.size(),Z);
  } else { int q=0; if(getenv("LEFTPRE")) for(char*p=getenv("LEFTPRE");*p;p++) q=D[q][*p-'0']; addeps(Nid(q,q0s),Sbase); addeps(Sbase+pre.size(),U); }
  for(int f=0;f<6;f++)for(int b=0;b<2;b++){ if(th[f][b]||td[f][b]<0)continue; int w=tw[f][b],t=tt[f][b];
    for(int q=0;q<n;q++) addeps(Nid(D[q][w],t),Bid(q,f,b)); }
  long facts=0;
  while(!wl.empty()){
    auto [Y,Zn]=wl.front(); wl.pop_front(); facts++;
    for(size_t i=0;i<epred[Y].size();i++) add(epred[Y][i],Zn);
    if(Y<6*n){ int q=Y/6,f=Y%6;
      if(th[f][0] && Zn==ACC){ printf("early HALT: dfa %d state %c reads blank\n",q,'A'+f); return 1; }
      if(getenv("PROG") && facts%1000000==0) fprintf(stderr,"facts %ld wl %zu\n",facts,wl.size());
      for(auto&e:lab[Zn]) addeps(Bid(q,f,e.first),e.second);
      if(Zn==ACC) addeps(Bid(q,f,0),ACC);
    }
  }
  // productive: nodes that can reach ACC by any edges
  vector<vector<int>> rev(NN);
  for(int X=0;X<NN;X++){ for(int Y:eset[X]) rev[Y].push_back(X); for(auto&e:lab[X]) rev[e.second].push_back(X);}
  vector<char> prod(NN,0); vector<int> st={ACC}; prod[ACC]=1;
  while(!st.empty()){int y=st.back();st.pop_back(); for(int x:rev[y]) if(!prod[x]){prod[x]=1;st.push_back(x);}}
  long tot=0; for(int X=0;X<NN;X++) tot+=cl[X].size();
  for(int q=0;q<n;q++)for(int f=0;f<6;f++)for(int b=0;b<2;b++){ if(!th[f][b])continue; int X=Nid(q,f);
    bool bad=false;
    if(b==0 && clset[X].count(ACC)) bad=true;
    for(int Zn:cl[X]) for(auto&e:lab[Zn]) if(e.first==b && prod[e.second]) bad=true;
    if(bad){ printf("HALT reachable: dfa state %d state %c reads %d  (nodes %d facts %ld)\n",q,'A'+f,b,NN,tot); return 1;}
  }
  printf("CLOSED n=%d nodes=%d facts=%ld\n",n,NN,tot); return 0;
}
