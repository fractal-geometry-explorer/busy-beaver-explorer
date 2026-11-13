// pds: pushdown closure decider ("direct FAR" with a lazily built DFA on one side).
//   pds MACHINE SIDE KIND PARAMS... [-m MAXTRANS]
//   SIDE = L or R: the half-tape that is abstracted (the other half, with the head cell, is an exact stack).
//   KIND = N n        : the last n cells
//          R r C M    : the last r runs, lengths exact below C and modulo M from C on
//          G r K MC C M : the last r groups of equal units (unit = 0^z 1^k), group counts exact below K and modulo MC
//                       from K on, lengths as for R; plus the unfinished unit
//          H r r0 r2 K MC C M : as G, but every group nearer than the nearest big group (count >= K) is kept, with that
//                       group and r0 groups beyond it, up to r2 groups in all
// Prints NONHALT / HALT / LIMIT and sizes.
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64; typedef unsigned int u32;
struct HSet{ vector<u64> t; size_t n=0, mask=0;
  HSet(){ t.assign(1<<16,~0ULL); mask=(1<<16)-1; }
  static inline u64 h(u64 x){ x^=x>>33; x*=0xff51afd7ed558ccdULL; x^=x>>33; x*=0xc4ceb9fe1a85ec53ULL; x^=x>>33; return x; }
  void grow(){ vector<u64> o; o.swap(t); t.assign(o.size()*2,~0ULL); mask=t.size()-1; for(u64 k:o) if(k!=~0ULL){ size_t i=h(k)&mask; while(t[i]!=~0ULL) i=(i+1)&mask; t[i]=k; } }
  pair<int,bool> insert(u64 k){ if((n+1)*10>t.size()*7) grow(); size_t i=h(k)&mask; while(t[i]!=~0ULL){ if(t[i]==k) return {0,false}; i=(i+1)&mask; } t[i]=k; n++; return {0,true}; }
  size_t size()const{return n;} };
static int Tw[6][2],Td[6][2],Tn[6][2];
static int KIND,PN,PR,PC,PM,PK,PMC,PR0=0,PR2=0;
static inline int inclen(int l){ if(l==255) return 255; l++; if(l>=PC) l=PC+((l-PC)%PM); return l; }
static unordered_map<string,int> sumid; static vector<string> sums;
static int intern(const string&s){auto it=sumid.find(s); if(it!=sumid.end())return it->second; int id=sums.size(); sums.push_back(s); sumid.emplace(s,id); return id;}
static unordered_map<u64,int> pushmemo;
static int pushsum(int q,int b){
  u64 k=((u64)q<<1)|b; auto it=pushmemo.find(k); if(it!=pushmemo.end())return it->second;
  string s=sums[q]; string r;
  if(KIND=='N'){ r=s.substr(1)+(char)('0'+b); }
  else if(KIND=='G'){ // groups (uz,uk,cnt)*, then z,k
    int n=s.size(); int z=(unsigned char)s[n-2], k=(unsigned char)s[n-1]; r=s.substr(0,n-2);
    if(b==1){ k=inclen(k); }
    else if(k==0){ z=inclen(z); }
    else {
      int g=r.size();
      if(g>=3 && (unsigned char)r[g-3]==z && (unsigned char)r[g-2]==k){ int c=(unsigned char)r[g-1]+1; if(c>=PK) c=PK+((c-PK)%PMC); r[g-1]=(char)c; }
      else { r.push_back((char)z); r.push_back((char)k); r.push_back((char)1); }
      { int len=r.size()/3; int keep=len-PR;
        if(PR2>0){ int j=-1; for(int i=len-1;i>=0;i--) if((unsigned char)r[3*i+2]>=PK){j=i;break;}
          if(j>=0) keep=min(keep,j-PR0); keep=max(keep,len-PR2); }
        if(keep>0) r=r.substr(3*keep); }
      z=1;k=0;
    }
    r.push_back((char)z); r.push_back((char)k);
  }
  else { // runs: pairs of bytes (bit, len) ; len 255 = INF
    int n=s.size()/2; unsigned char lb=s[2*n-2], ll=(unsigned char)s[2*n-1];
    if(lb==b){ r=s; if(ll!=255){ int l=ll+1; if(l>=PC) l=PC+((l-PC)%PM); r[2*n-1]=(char)l; } }
    else { r=s; r.push_back((char)b); r.push_back((char)1); if(n+1>PR) r=r.substr(2); }
  }
  int id=intern(r); pushmemo.emplace(k,id); return id;
}
// automaton states: interned
static unordered_map<u64,int> stid; static int nst=0;
static int st_of(u64 key){auto it=stid.find(key); if(it!=stid.end())return it->second; stid.emplace(key,nst); return nst++;}
// key kinds: control (q,f): 0 ; mid (p2state,x): 1 ; mid2 (s): 2 ; final: 3
static inline int ctrl(int q,int f){return st_of(((u64)0<<60)|((u64)q*6+f));}
static HSet trans; // (p<<33)|(g<<31)|s   p,s < 2^31
struct Tr{int p,g,s;};
static vector<Tr> work;
static vector<vector<pair<int,int>>> outv; // out[s] = (g,s2)
static vector<vector<int>> epsv; static HSet epsset;
static vector<vector<pair<int,int>>> pred; static HSet predset; // by summary
static vector<vector<Tr>> byq;
static vector<int> st_q, st_f; // for control states: summary and tm state; -1 otherwise
static void ensure_st(int s){ if((int)outv.size()<=s){outv.resize(s+1);epsv.resize(s+1);st_q.resize(s+1,-1);st_f.resize(s+1,-1);} }
static int mkctrl(int q,int f){int s=ctrl(q,f); ensure_st(s); st_q[s]=q; st_f[s]=f; return s;}
static void ensure_q(int q){ if((int)pred.size()<=q){pred.resize(q+1);byq.resize(q+1);} }
static inline void add(int p,int g,int s){
  u64 k=((u64)p<<33)|((u64)g<<31)|(u64)s;
  if(trans.insert(k).second){ ensure_st(max(p,s)); outv[p].push_back({g,s}); work.push_back({p,g,s}); }
}
static void add_eps(int p,int s){
  u64 k=((u64)p<<32)|(u64)s;
  if(epsset.insert(k).second){ ensure_st(max(p,s)); epsv[s].push_back(p); for(size_t i=0;i<outv[s].size();i++){auto o=outv[s][i]; add(p,o.first,o.second);} }
}
static int absdir;
static void apply_abs(const Tr&t,int q2,int x){
  int f=st_f[t.p]; int b=t.g==2?0:t.g; int w=Tw[f][b], ns=Tn[f][b];
  int p2=mkctrl(q2,ns); int mid=st_of(((u64)1<<60)|((u64)p2<<1)|x); ensure_st(mid);
  add(p2,x,mid);
  if(t.g==2){ int mid2=st_of(((u64)2<<60)|(u64)t.s); ensure_st(mid2); add(mid,w,mid2); add(mid2,2,t.s); }
  else add(mid,w,t.s);
}
int main(int argc,char**argv){
  char*m=argv[1]; int side=argv[2][0]; KIND=argv[3][0]; u64 maxtrans=400000000ULL;
  int ai=4;
  if(KIND=='N'){PN=atoi(argv[ai++]);} else if(KIND=='H'){KIND='G';PR=atoi(argv[ai++]);PR0=atoi(argv[ai++]);PR2=atoi(argv[ai++]);PK=atoi(argv[ai++]);PMC=atoi(argv[ai++]);PC=atoi(argv[ai++]);PM=atoi(argv[ai++]);} else if(KIND=='G'){PR=atoi(argv[ai++]);PK=atoi(argv[ai++]);PMC=atoi(argv[ai++]);PC=atoi(argv[ai++]);PM=atoi(argv[ai++]);} else {PR=atoi(argv[ai++]);PC=atoi(argv[ai++]);PM=atoi(argv[ai++]);}
  const char*itape=0; int ist=0;
  for(;ai<argc;ai++){ if(!strcmp(argv[ai],"-m")) maxtrans=strtoull(argv[++ai],0,10); else if(!strcmp(argv[ai],"-i")){ itape=argv[++ai]; ist=argv[++ai][0]-'A'; } }
  for(int i=0;i<6;i++)for(int b=0;b<2;b++){char*s=m+7*i+3*b; if(s[2]=='-'){Tn[i][b]=-1;continue;} Tw[i][b]=s[0]-'0'; Td[i][b]=s[1]=='R'?1:-1; Tn[i][b]=s[2]-'A';}
  absdir = side=='L'?-1:1;
  string blank; if(KIND=='N') blank=string(PN,'0'); else if(KIND=='G'){ blank.push_back((char)255); blank.push_back((char)0); } else { blank.push_back((char)0); blank.push_back((char)255); }
  int q0=intern(blank); ensure_q(q0); pred[q0].push_back({q0,0}); predset.insert(((u64)q0<<33)|((u64)q0<<1)|0);
  int FINAL=st_of((u64)3<<60); ensure_st(FINAL);
  // -i TAPE STATE: start with the head on the blank cell next to TAPE, which lies on the abstract side (near cell first
  // for side R: TAPE is written left to right and the head is left of it; for side L the head is right of it)
  int qi=q0;
  if(itape){ int n=strlen(itape); for(int i=0;i<n;i++){ int b=(side=='R'? itape[n-1-i]:itape[i])-'0'; int nq=pushsum(qi,b); ensure_q(max(nq,qi)); u64 pk=((u64)nq<<33)|((u64)qi<<1)|b; if(predset.insert(pk).second) pred[nq].push_back({qi,b}); qi=nq; } }
  add(mkctrl(qi,ist),2,FINAL);
  clock_t t0=clock(); unsigned long long iter=0; const char*res="NONHALT"; Tr halt{0,0,0};
  while(!work.empty()){
    Tr t=work.back(); work.pop_back();
    for(size_t i=0;i<epsv[t.p].size();i++) add(epsv[t.p][i],t.g,t.s);
    if(st_q[t.p]<0) continue;
    int q=st_q[t.p], f=st_f[t.p]; int b=t.g==2?0:t.g;
    if(Tn[f][b]<0){res="HALT";halt=t;break;}
    int w=Tw[f][b], d=Td[f][b], ns=Tn[f][b];
    if(d==absdir){
      ensure_q(q); byq[q].push_back(t);
      for(size_t i=0;i<pred[q].size();i++){auto pr=pred[q][i]; apply_abs(t,pr.first,pr.second);}
    } else {
      int nq=pushsum(q,w); ensure_q(max(nq,q));
      u64 pk=((u64)nq<<33)|((u64)q<<1)|w;
      if(predset.insert(pk).second){ pred[nq].push_back({q,w}); for(size_t i=0;i<byq[nq].size();i++){Tr xt=byq[nq][i]; apply_abs(xt,q,w);} }
      int p2=mkctrl(nq,ns);
      if(t.g==2) add(p2,2,t.s); else add_eps(p2,t.s);
    }
    if(trans.size()>maxtrans){res="LIMIT";break;}
    if((++iter&0xFFFFFF)==0){ fprintf(stderr,"trans=%zu work=%zu summaries=%zu preds=%zu t=%.0fs\n",trans.size(),work.size(),sums.size(),predset.size(),(double)(clock()-t0)/CLOCKS_PER_SEC); }
  }
  printf("%s trans=%zu summaries=%zu states=%d preds=%zu time=%.1fs",res,trans.size(),sums.size(),nst,predset.size(),(double)(clock()-t0)/CLOCKS_PER_SEC);
  if(!strcmp(res,"HALT")){ printf(" halt: state %c top %d summary ",'A'+st_f[halt.p],halt.g); string s=sums[st_q[halt.p]]; if(KIND=='N')printf("%s",s.c_str()); else if(KIND=='G'){ size_t n=s.size(); for(size_t i=0;i+2<n;i+=3)printf("(0^%d 1^%d)^%d ",(unsigned char)s[i],(unsigned char)s[i+1],(unsigned char)s[i+2]); printf("0^%d 1^%d",(unsigned char)s[n-2],(unsigned char)s[n-1]); } else for(size_t i=0;i<s.size();i+=2)printf("%d^%d ",s[i],(unsigned char)s[i+1]); }
  printf("\n");
  if(getenv("DUMP")&&KIND=='G'){ map<int,int> hl,hz; srand(1);
    for(auto&x:sums){ int ml=0,mz=0; size_t n=x.size(); for(size_t i=0;i+2<n;i+=3){ if((unsigned char)x[i]!=255) mz=max(mz,(int)(unsigned char)x[i]); ml=max(ml,(int)(unsigned char)x[i+1]); } ml=max(ml,(int)(unsigned char)x[n-1]); if((unsigned char)x[n-2]!=255) mz=max(mz,(int)(unsigned char)x[n-2]); hl[ml]++; hz[mz]++; }
    printf("maxlen hist:"); for(auto&p:hl)printf(" %d:%d",p.first,p.second); printf("\nmaxzero hist:"); for(auto&p:hz)printf(" %d:%d",p.first,p.second); printf("\n");
    for(int j=0;j<atoi(getenv("DUMP"));j++){ string x=sums[rand()%sums.size()]; size_t n=x.size(); for(size_t i=0;i+2<n;i+=3)printf("(0^%d 1^%d)^%d ",(unsigned char)x[i],(unsigned char)x[i+1],(unsigned char)x[i+2]); printf("0^%d 1^%d\n",(unsigned char)x[n-2],(unsigned char)x[n-1]); } }
  return 0;
}
