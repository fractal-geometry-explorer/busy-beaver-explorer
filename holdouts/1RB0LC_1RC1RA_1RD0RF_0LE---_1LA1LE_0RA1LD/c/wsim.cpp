// wsim: 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD from blank tape on a zipper tape whose items are cells or blocks of
// words (01 / 011). Shortcuts, theorems of lean/Pulse.lean for every tape around:
//   right_words  A> ws R           -> images(ws) A> R      2 steps per 01, 5 per 011
//   left_words   images(ws) A>111  -> A>111 ws             8 steps per 01, 5 per 011
// A block is crossed by either rule in one move. Where the head meets a block in any other way, one word is peeled
// off the near end into cells. Adjacent blocks in the same form are merged (smaller into larger).
// usage: wsim MAXSTEPS [LOGFILE|-] [SECONDS] [MINW]   LOGFILE: "step hash len" at every return to the left end in the
//        form C>0 (011)^a 001101 ..., in the format of psim.c, for comparison (logging costs O(tape) per return).
// build: g++ -O2 -std=c++17 -o wsim wsim.cpp
#include <bits/stdc++.h>
using namespace std; typedef long long ll; typedef unsigned long long ull;
struct Blk { deque<uint8_t> w; ll cells=0, n2=0; bool img=false; };
static vector<Blk> B; static vector<int> fr;
static int nb(){ if(!fr.empty()){int i=fr.back(); fr.pop_back(); return i;} B.emplace_back(); return (int)B.size()-1; }
static void del(int i){ deque<uint8_t>().swap(B[i].w); B[i].cells=B[i].n2=0; B[i].img=false; fr.push_back(i); }
static inline ll nw(const Blk&b){ return (ll)b.w.size(); }
static inline ll crs(const Blk&b){ return 2*(nw(b)-b.n2)+5*b.n2; }
static inline ll cls(const Blk&b){ return 8*(nw(b)-b.n2)+5*b.n2; }
// cells of one word in left-to-right order
static int wcells(uint8_t ty, bool img, uint8_t*c){ if(!img){ if(ty){c[0]=0;c[1]=1;c[2]=1;return 3;} c[0]=0;c[1]=1;return 2; }
  if(ty){c[0]=1;c[1]=0;c[2]=0;return 3;} c[0]=1;c[1]=1;return 2; }
// merge block b (right) into a (left) or vice versa; returns surviving id
static int merge(int a,int b){ Blk&A=B[a]; Blk&Bb=B[b];
  if(A.w.size()>=Bb.w.size()){ for(auto x:Bb.w) A.w.push_back(x); A.cells+=Bb.cells; A.n2+=Bb.n2; del(b); return a; }
  for(auto it=A.w.rbegin(); it!=A.w.rend(); ++it) Bb.w.push_front(*it); Bb.cells+=A.cells; Bb.n2+=A.n2; del(a); return b; }
int main(int argc,char**argv){
 const char*mm="1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD"; int W[6][2],D[6][2],N[6][2];
 for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*x=mm+7*s+3*b; if(x[0]=='-'){N[s][b]=-1;continue;} W[s][b]=x[0]-'0';D[s][b]=x[1]=='R'?1:-1;N[s][b]=x[2]-'A';}
 ll MAX=(ll)atof(argv[1]); FILE*lg=argc>2&&strcmp(argv[2],"-")?fopen(argv[2],"w"):0; double SECS=argc>3?atof(argv[3]):1e18; ll MINW=argc>4?atoll(argv[4]):8;
 vector<int> L,R; int h=0, st=0; ll p=0,lo=0,hi=0,k=0; ll ncr=0,ncl=0,npeel=0,nmk=0,nX=0,nv=0,dsteps=0; uint8_t wc[4];
 auto t0=chrono::steady_clock::now(); auto el=[&](){return chrono::duration<double>(chrono::steady_clock::now()-t0).count();}; ll nextrep=1000000;
 vector<uint8_t> flat,tmp;
 auto cellAt=[&](vector<int>&S,size_t d)->int{ if(d>=S.size()) return 0; int x=S[S.size()-1-d]; return x<2?x:-1; };
 // push a block onto L (imaged, after right crossing) merging with L top if imaged block
 auto pushL=[&](int id){ if(!L.empty()&&L.back()>=2&&B[L.back()-2].img==B[id].img){ int a=L.back()-2; L.pop_back(); id=merge(a,id);} L.push_back(id+2); };
 auto pushR=[&](int id){ if(!R.empty()&&R.back()>=2&&B[R.back()-2].img==B[id].img){ int b=R.back()-2; R.pop_back(); id=merge(id,b);} R.push_back(id+2); };
 for(;;){
  if(k>=MAX) break;
  // left_words over an imaged block left of the packet
  if(st==0 && h==1 && !L.empty() && L.back()>=2 && B[L.back()-2].img && cellAt(R,0)==1 && cellAt(R,1)==1){
    int id=L.back()-2; L.pop_back(); Blk&b=B[id]; b.img=false; R.pop_back(); R.pop_back(); ll c=b.cells, s=cls(b); pushR(id); R.push_back(1); R.push_back(1);
    p-=c; k+=s; ncl++; if(p<lo)lo=p; continue; }
  // packing raw images left of the packet into an imaged block
  if(st==0 && h==1 && cellAt(R,0)==1 && cellAt(R,1)==1 && !L.empty() && L.back()<2){
    size_t d=0; vector<uint8_t> ws;
    for(;;){ int a=cellAt(L,d), b=cellAt(L,d+1); if(a==1&&b==1){ ws.push_back(0); d+=2; continue; }
      int c=cellAt(L,d+2); if(a==0&&b==0&&c==1){ ws.push_back(1); d+=3; continue; } break; }
    if(d>0 && d<=L.size()){ int id=nb(); Blk&b=B[id]; for(size_t j=ws.size();j-->0;){ b.w.push_back(ws[j]); b.n2+=ws[j]; } b.cells=d; b.img=true; L.resize(L.size()-d); pushL(id); nmk++; continue; }
  }
  // packing: A on 0, raw words ahead
  if(st==0 && h==0 && cellAt(R,0)==1){
    auto rc=[&](size_t j)->int{ return j==0?0:cellAt(R,j-1); };
    size_t i=0; ll n=0;
    for(;;){ int c0=rc(i),c1=rc(i+1),c2=rc(i+2); if(c0!=0||c1!=1||c2<0) break; if(c2==1) i+=3; else i+=2; n++; }
    bool blkafter = (i>=2) && (R.size()>=i) && (R.size()>i-1) && R[R.size()-1-(i-1)]>=2 && !B[R[R.size()-1-(i-1)]-2].img;
    if((ll)i>=MINW || blkafter){
      int id=nb(); Blk&b=B[id]; size_t j=0; while(j<i){ int c2=rc(j+2); if(c2==1){ b.w.push_back(1); b.n2++; j+=3; } else { b.w.push_back(0); j+=2; } } b.cells=i; b.img=false;
      R.resize(R.size()-(i-1)); pushR(id); nmk++;
      // head is on the block's first cell: take it as the next item below
      h=-1; }
  }
  if(h>=0){
   int ns=N[st][h]; k++; dsteps++; if(ns<0){ printf("HALT at step %lld\n",k); fflush(stdout); return 0; }
   int w=W[st][h], dir=D[st][h]; st=ns;
   if(dir>0){ L.push_back(w); p++; if(p>hi)hi=p; }
   else { R.push_back(w); p--; if(p<lo)lo=p;
     // fetch from L
     for(;;){ if(L.empty()){h=0;break;} int x=L.back(); if(x<2){L.pop_back();h=x;break;}
       Blk&bk=B[x-2]; uint8_t ty=bk.w.back(); bk.w.pop_back(); int n=wcells(ty,bk.img,wc); bk.cells-=n; bk.n2-=ty; if(bk.w.empty()){L.pop_back(); del(x-2);} for(int j=0;j<n;j++) L.push_back(wc[j]); npeel++; }
     if(st==2&&p==lo){ nv++;
       if(lg){ flat.clear(); flat.push_back(h); for(size_t j=R.size();j-->0;){ int x=R[j]; if(x<2) flat.push_back(x); else { Blk&bk=B[x-2]; for(auto ty:bk.w){ int n=wcells(ty,bk.img,wc); for(int q=0;q<n;q++) flat.push_back(wc[q]); } } }
         ll len=hi-lo; while((ll)flat.size()<len+1) flat.push_back(0); flat.resize(len+1);
         size_t q=1; while(q+2<flat.size()&&flat[q]==0&&flat[q+1]==1&&flat[q+2]==1) q+=3;
         if(q+5<flat.size()&&flat[q]==0&&flat[q+1]==0&&flat[q+2]==1&&flat[q+3]==1&&flat[q+4]==0&&flat[q+5]==1){ nX++; ull hh=1469598103934665603ULL; for(auto c:flat) hh=(hh^c)*1099511628211ULL; fprintf(lg,"%lld %llx %lld\n",k,hh,len);} }
       if((nv&255)==0 && el()>SECS) break;
       if(k>=nextrep){ fprintf(stderr,"%.0f s step %lld (10^%.2f) len %lld items %zu+%zu blocks %zu cross %lld/%lld peel %lld made %lld direct %lld\n",el(),k,log10((double)k),hi-lo,L.size(),R.size(),B.size()-fr.size(),ncr,ncl,npeel,nmk,dsteps); nextrep=k*2; }
     }
     continue; }
  }
  // fetch from R (after a right move, or after packing)
  for(;;){ if(R.empty()){h=0;break;} int x=R.back(); if(x<2){R.pop_back();h=x;break;}
    Blk&bk=B[x-2];
    if(st==0 && !bk.img){ R.pop_back(); bk.img=true; ll c=bk.cells, s=crs(bk); pushL(x-2); p+=c; k+=s; ncr++; if(p>hi)hi=p; continue; }
    uint8_t ty=bk.w.front(); bk.w.pop_front(); int n=wcells(ty,bk.img,wc); bk.cells-=n; bk.n2-=ty; if(bk.w.empty()){R.pop_back(); del(x-2);} for(int j=n;j-->0;) R.push_back(wc[j]); npeel++; }
 }
 printf("no halt in %lld steps; len %lld; X %lld; crossings %lld/%lld peel %lld made %lld direct %lld; %.1f s\n",k,hi-lo,nX,ncr,ncl,npeel,nmk,dsteps,el()); return 0; }
