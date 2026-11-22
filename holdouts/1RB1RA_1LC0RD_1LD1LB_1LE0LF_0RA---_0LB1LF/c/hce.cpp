// hce.cpp: halving-chain engine for 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF (via G = 1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB1LE,
// which halts exactly when D reads 0 with a 1 on its left).
// Tape = L stack + head gadget + R stack of tokens. Tokens: D n = 1(11)^n00 (right side form), S n = 1(01)^(n+1) (left side
// form), B bits (raw), U (word)^count, G segment (a run of digits, crossed in O(1)).
// Modes: R = l A> 0100 r, L = l <B 1 r, J = l <C 100 r, X = plain head (state q, about to read the cell on side dir).
//
// Steps are counted in G (the machine itself takes 2 more steps for each detour, so its count is never smaller).
// The engine is exact: crossing a digit or a segment uses the rules proved in ../lean/EngineRules.lean (pr93_rightD0,
// pr93_rightD, pr93_left, pr93_leftJ); every other move simulates a window of tokens cell by cell (cached), or, when a
// count in the window is large (> 12), applies a rule learned from five probe runs with counts base + 6t and an affine
// fit. ../py/prove_prules.py proves the learned rules for every t with symtm (exported by `hce export`). The run's
// jumps over repeated far passes (cycle detection, off with NOCYC=1) are validated, not proved.
// A halt is caught in the cell-by-cell windows; a window whose leftmost cell is D reading 0 grows first, so the cell
// to its left is known.
//
// build: g++ -O2 -std=c++17 -o hce hce.cpp
// usage: NOBLK=1 ./hce run SECONDS          report at 10^5, 10^6, ... steps, stop after SECONDS or at a halt
//        NOBLK=1 ./hce check N1 N2 ...      compare the tape with direct simulation of G after about N steps
//        NOBLK=1 ./hce export N RULES.txt   run to N steps and write the learned rules (for py/prove_prules.py)
//        (NOBLK=1: no block tokens; blocks are slower here.  BIGWIN=1: report windows of over 10^6 cells.
//        Other commands are for exploration.)
#include <bits/stdc++.h>
using namespace std;
typedef long long ll; typedef __int128 i128;
static string i2s(i128 x){ if(x==0) return "0"; bool ng=x<0; if(ng)x=-x; string s; while(x>0){s+=char('0'+(int)(x%10)); x/=10;} if(ng)s+='-'; reverse(s.begin(),s.end()); return s; }

// ---------------------------------------------------------------- machine G
// states A..E = 0..4
static const int TW[5][2]={{1,1},{1,0},{1,1},{1,0},{0,1}};
static const int TM[5][2]={{1,1},{-1,1},{-1,-1},{1,-1},{-1,-1}};
static const int TQ[5][2]={{1,0},{2,3},{3,1},{0,4},{1,4}};

// ---------------------------------------------------------------- tokens
// RunDeque: a deque of digits stored as front literals + runs (pattern)^count + back literals
struct Run { vector<ll> pat; ll c; };
// Compact storage: run headers (count, pattern length) and all patterns' digits in one deque, in tape order. A run
// with count 1 is a literal block; neighbouring literal blocks merge (MERGELIT), so a literal digit costs 8 bytes.
// Invariant: a run with count > 1 has a pattern of at most PMAX digits.
static bool MERGELIT=false;
struct RH { ll c; uint32_t len; };
struct RunDeque {
    deque<ll> fb, bb; deque<RH> rh; deque<ll> pd; ll n=0;
    static const int FBMAX=16, PMAX=8;
    size_t size() const { return n; } bool empty() const { return n==0; }
    void clear(){ fb.clear(); bb.clear(); rh.clear(); pd.clear(); n=0; }
    void shrink_to_fit(){ deque<ll>().swap(fb); deque<ll>().swap(bb); deque<RH>().swap(rh); deque<ll>().swap(pd); }
    void set2(ll a, ll b){ clear(); fb.push_back(a); fb.push_back(b); n=2; }
    size_t nruns() const { return rh.size(); }
    // offset of run i in pd
    size_t off(size_t i) const { if(i<rh.size()/2){ size_t o=0; for(size_t j=0;j<i;j++) o+=rh[j].len; return o; }
        size_t o=pd.size(); for(size_t j=rh.size(); j>i; j--) o-=rh[j-1].len; return o; }
    Run run(size_t i) const { Run r; size_t o=off(i); r.pat.assign(pd.begin()+o, pd.begin()+o+rh[i].len); r.c=rh[i].c; return r; }
    ll& cnt(size_t i){ return rh[i].c; }
    bool frontIs(const ll* p, int len) const { if(rh.empty() || (int)rh.front().len!=len) return false; for(int i=0;i<len;i++) if(pd[i]!=p[i]) return false; return true; }
    bool backIs(const ll* p, int len) const { if(rh.empty() || (int)rh.back().len!=len) return false; size_t o=pd.size()-len; for(int i=0;i<len;i++) if(pd[o+i]!=p[i]) return false; return true; }
    void runPushFront(const ll* p, int len, ll c){
        if(len<=PMAX && frontIs(p,len) && (rh.front().c>1 || len<=PMAX)){ rh.front().c+=c; return; }
        if(MERGELIT && c==1 && !rh.empty() && rh.front().c==1){ for(int i=len-1;i>=0;i--) pd.push_front(p[i]); rh.front().len+=len; return; }
        for(int i=len-1;i>=0;i--) pd.push_front(p[i]); rh.push_front({c,(uint32_t)len});
    }
    void runPushBack(const ll* p, int len, ll c){
        if(len<=PMAX && backIs(p,len)){ rh.back().c+=c; return; }
        if(MERGELIT && c==1 && !rh.empty() && rh.back().c==1){ for(int i=0;i<len;i++) pd.push_back(p[i]); rh.back().len+=len; return; }
        for(int i=0;i<len;i++) pd.push_back(p[i]); rh.push_back({c,(uint32_t)len});
    }
    void tidyFront(){
        bool ch=true; ll buf[2*PMAX];
        while(ch){ ch=false;
            for(int p=1;p<=PMAX && !ch;p++){
                if((int)fb.size()<p) break;
                long s=fb.size()-p;
                for(int i=0;i<p;i++) buf[i]=fb[s+i];
                if(frontIs(buf,p)){ rh.front().c++; fb.resize(s); ch=true; break; }
                if((int)fb.size()>=2*p){ long s2=fb.size()-2*p; bool eq=true; for(int i=0;i<p;i++) if(fb[s2+i]!=fb[s2+p+i]){eq=false;break;}
                    if(eq){ fb.resize(s2); runPushFront(buf,p,2); ch=true; break; } }
            }
        }
        while((int)fb.size()>FBMAX){ ll x=fb.back(); fb.pop_back(); runPushFront(&x,1,1); }
    }
    void tidyBack(){
        bool ch=true; ll buf[2*PMAX];
        while(ch){ ch=false;
            for(int p=1;p<=PMAX && !ch;p++){
                if((int)bb.size()<p) break;
                for(int i=0;i<p;i++) buf[i]=bb[i];
                if(backIs(buf,p)){ rh.back().c++; bb.erase(bb.begin(),bb.begin()+p); ch=true; break; }
                if((int)bb.size()>=2*p){ bool eq=true; for(int i=0;i<p;i++) if(bb[i]!=bb[p+i]){eq=false;break;}
                    if(eq){ bb.erase(bb.begin(),bb.begin()+2*p); runPushBack(buf,p,2); ch=true; break; } }
            }
        }
        while((int)bb.size()>FBMAX){ ll x=bb.front(); bb.pop_front(); runPushBack(&x,1,1); }
    }
    void push_front(ll d){ fb.push_front(d); n++; tidyFront(); }
    void push_back(ll d){ bb.push_back(d); n++; tidyBack(); }
    ll front() const { if(!fb.empty()) return fb.front(); if(!rh.empty()) return pd.front(); return bb.front(); }
    ll back() const { if(!bb.empty()) return bb.back(); if(!rh.empty()) return pd.back(); return fb.back(); }
    void pop_front(){
        n--;
        if(!fb.empty()){ fb.pop_front(); return; }
        if(!rh.empty()){ RH& r=rh.front();
            if(r.c==1){ pd.pop_front(); if(--r.len==0) rh.pop_front(); return; }
            r.c--; int len=r.len; for(int i=len-1;i>=1;i--) fb.push_front(pd[i]); return; }
        bb.pop_front();
    }
    void pop_back(){
        n--;
        if(!bb.empty()){ bb.pop_back(); return; }
        if(!rh.empty()){ RH& r=rh.back();
            if(r.c==1){ pd.pop_back(); if(--r.len==0) rh.pop_back(); return; }
            r.c--; int len=r.len; size_t o=pd.size()-len; for(int i=0;i+1<len;i++) bb.push_back(pd[o+i]); return; }
        fb.pop_back();
    }
    void flushFront(){ while(!fb.empty()){ ll x=fb.back(); fb.pop_back(); runPushFront(&x,1,1); } }
    void flushBack(){ while(!bb.empty()){ ll x=bb.front(); bb.pop_front(); runPushBack(&x,1,1); } }
    // append o (to the right of this) into this
    void appendRight(RunDeque& o){ flushBack(); o.flushFront(); vector<ll> p; size_t k=0;
        for(auto& h: o.rh){ p.assign(o.pd.begin()+k, o.pd.begin()+k+h.len); k+=h.len; runPushBack(p.data(),h.len,h.c); }
        bb.swap(o.bb); n+=o.n; o.clear(); }
    // prepend o (to the left of this) into this
    void prependLeft(RunDeque& o){ flushFront(); o.flushBack(); vector<ll> p; size_t k=o.pd.size();
        for(auto it=o.rh.rbegin(); it!=o.rh.rend(); ++it){ k-=it->len; p.assign(o.pd.begin()+k, o.pd.begin()+k+it->len); runPushFront(p.data(),it->len,it->c); }
        fb.swap(o.fb); n+=o.n; o.clear(); }
    vector<ll> digits() const { vector<ll> v(fb.begin(),fb.end()); size_t k=0; for(auto& h: rh){ for(ll c=0;c<h.c;c++) for(size_t i=0;i<h.len;i++) v.push_back(pd[k+i]); k+=h.len; } for(ll x: bb) v.push_back(x); return v; }
};
struct Seg { RunDeque ds; i128 sm=0; };
struct SegPool { vector<unique_ptr<Seg>> v; Seg& operator[](size_t i){ return *v[i]; } size_t size() const { return v.size(); } };
static SegPool pool; static vector<int> freelist;   // a deleted segment's memory is freed
static int newseg(){ if(!freelist.empty()){ int i=freelist.back(); freelist.pop_back(); pool.v[i]=make_unique<Seg>(); return i;} pool.v.push_back(make_unique<Seg>()); return pool.size()-1; }
static void delseg(int i){ pool.v[i].reset(); freelist.push_back(i); }
enum { KD='D', KS='S', KB='B', KU='U', KG='G', KK='K' };
struct Tok { char k; ll n; string w; int g; };
struct Blk { vector<Tok> per; string key; string bits; };
static vector<Blk> bpool; static unordered_map<string,int> bintern;
static Tok TD(ll n){ return {KD,n,"",-1}; } static Tok TS(ll n){ return {KS,n,"",-1}; }
static Tok TB(const string& w){ return {KB,0,w,-1}; } static Tok TU(const string& w, ll c){ return {KU,c,w,-1}; }
static string rep(const string& w, ll c){ string s; s.reserve(w.size()*c); for(ll i=0;i<c;i++) s+=w; return s; }
static string tbits(const Tok& t, bool left){
    switch(t.k){
        case KD: return "1"+rep("11",t.n)+"00";
        case KS: return "1"+rep("01",t.n+1);
        case KB: return t.w;
        case KU: return rep(t.w,t.n);
        case KK: return rep(bpool[t.g].bits,t.n);
        default: { string s; for(ll n: pool[t.g].ds.digits()) s+= left? "1"+rep("01",n+1) : "1"+rep("11",n)+"00"; return s; }
    }
}
static string tstr(const Tok& t){
    switch(t.k){ case KD: return "D"+to_string(t.n); case KS: return "S"+to_string(t.n); case KB: return t.w;
        case KU: return "("+t.w+")^"+to_string(t.n); case KK: return "{"+bpool[t.g].key+"}^"+to_string(t.n); default: return "G["+to_string(pool[t.g].ds.size())+"]"; }
}
static int internBlk(const vector<Tok>& per, bool left){
    string k; for(auto&t:per){ if(!k.empty()) k+=' '; k+=tstr(t); }
    k = (left?"L:":"R:")+k;
    auto it=bintern.find(k); if(it!=bintern.end()) return it->second;
    Blk b; b.per=per; b.key=k; for(auto&t:per) b.bits+=tbits(t,left); bpool.push_back(b); int id=bpool.size()-1; bintern[k]=id; return id;
}
// ---------------------------------------------------------------- parsing
static void pushraw(vector<Tok>& out, const string& s){ if(s.empty()) return; if(!out.empty() && out.back().k==KB) out.back().w+=s; else out.push_back(TB(s)); }
// compress B tokens: runs of a period-1 word (len>=8) or period-2 word (count>=5) become U tokens
static vector<Tok> compressB(const vector<Tok>& in){
    vector<Tok> out;
    for(const Tok& t: in){
        if(t.k!=KB){ out.push_back(t); continue; }
        const string& s=t.w; size_t i=0, n=s.size(); string loose;
        while(i<n){
            size_t j=i; while(j<n && s[j]==s[i]) j++;
            size_t r1=j-i;
            size_t k=i; while(k+1<n && s[k]==s[i] && s[k+1]==s[i+1<n?i+1:i] && s[i]!=s[i+1<n?i+1:i]) k+=2;
            size_t r2=(i+1<n && s[i]!=s[i+1])? (k-i)/2 : 0;
            if(r1>=8 && r1>=2*r2){ if(!loose.empty()){ pushraw(out,loose); loose.clear(); } out.push_back(TU(string(1,s[i]),r1)); i=j; }
            else if(r2>=5){ if(!loose.empty()){ pushraw(out,loose); loose.clear(); } out.push_back(TU(s.substr(i,2),r2)); i+=2*r2; }
            else { loose+=s[i]; i++; }
        }
        if(!loose.empty()) pushraw(out,loose);
    }
    return out;
}
static vector<Tok> parse_right(const string& s){
    vector<Tok> out; size_t i=0,n=s.size();
    while(i<n){
        size_t j=i;
        if(s[i]=='1'){ while(j<n&&s[j]=='1') j++; size_t k=j-i;
            if(k%2==1 && j+1<n && s[j]=='0' && s[j+1]=='0'){ out.push_back(TD((k-1)/2)); i=j+2; continue; } }
        else { while(j<n&&s[j]=='0') j++; }
        pushraw(out,s.substr(i,j-i)); i=j;
    }
    return compressB(out);
}
static vector<Tok> parse_left(const string& s){
    vector<Tok> rev; long j=s.size();
    while(j>0){
        long m=0,i=j; while(i-2>=0 && s[i-2]=='0' && s[i-1]=='1'){ i-=2; m++; }
        if(m>=1 && i-1>=0 && s[i-1]=='1'){ rev.push_back(TS(m-1)); j=i-1; continue; }
        if(!rev.empty() && rev.back().k==KB) rev.back().w=s[j-1]+rev.back().w; else rev.push_back(TB(string(1,s[j-1])));
        j--;
    }
    reverse(rev.begin(),rev.end()); return compressB(rev);
}
// ---------------------------------------------------------------- raw simulation on a bit window
struct RawRes { ll n=0; string lp, rp; int keepR=-1; int keepL=0; char mode='X'; int q=0; int dir=1; bool halt=false; bool toolong=false; bool grow=false; };
// t: window bits; pos: head; lend/rend: window reaches the tape end on that side; rb: right token boundaries (cumulative
// positions, ascending, 1-based token counts), lb: left token boundaries (cumulative from window start).
static RawRes rawsim(string t, long pos, int q, bool lend, bool rend, const vector<long>& rbv, const vector<long>& lbv, ll maxn){
    RawRes R; long off=0, mx=pos, mn=pos; ll n=0;
    unordered_map<long,int> rb, lb; for(size_t i=0;i<rbv.size();i++) rb[rbv[i]]=i+1; for(size_t i=0;i<lbv.size();i++) lb[lbv[i]]=i+1;
    long rbmax = rbv.empty()?0:rbv.back();
    while(true){
        if(pos<0){
            if(!lend){
                R.n=n; R.q=q; R.dir=-1; R.lp="";
                if(q==1 && t.size()>=1 && t[0]=='1'){ R.mode='L'; R.rp=t.substr(1); }
                else if(q==2 && t.size()>=3 && t.compare(0,3,"100")==0){ R.mode='J'; R.rp=t.substr(3); }
                else { R.mode='X'; R.rp=t; }
                R.keepR=-1; return R;
            }
            t.insert(t.begin(),'0'); pos=0; off++;
        }
        if(pos>=(long)t.size()){
            if(!rend){ R.n=n; R.q=q; R.dir=1; R.mode='X'; R.lp=t; R.rp=""; R.keepR=-1; return R; }
            t.push_back('0');
        }
        int c=t[pos]-'0';
        if(q==3 && c==0 && pos>0 && t[pos-1]=='1'){ R.halt=true; R.n=n; return R; }
        if(q==3 && c==0 && pos==0 && !lend){ R.grow=true; R.n=n; return R; } // the halting test needs the cell left of the window
        t[pos]='0'+TW[q][c]; int d=TM[q][c]; q=TQ[q][c]; pos+=d; n++;
        if(pos>mx) mx=pos;
        if(pos<mn){ mn=pos; long b=pos+1-off;
            auto it=lb.find(b);
            if(it!=lb.end() && pos+1<(long)t.size()){
                if(q==1 && t[pos+1]=='1'){ R.n=n; R.mode='L'; R.q=q; R.dir=-1; R.lp=t.substr(0,pos+1); R.rp=t.substr(pos+2); R.keepL=it->second; R.keepR=-1; return R; }
                if(q==2 && pos+3<(long)t.size() && t.compare(pos+1,3,"100")==0){ R.n=n; R.mode='J'; R.q=q; R.dir=-1; R.lp=t.substr(0,pos+1); R.rp=t.substr(pos+4); R.keepL=it->second; R.keepR=-1; return R; }
            }
        }
        if(q==0 && pos>=0){
            bool g=false;
            if(pos+4<=(long)t.size()) g = t.compare(pos,4,"0100")==0;
            else if(rend){ string x=t.substr(pos); while(x.size()<4) x+='0'; g = x=="0100"; }
            if(g){
                long b=pos+4-off;
                auto it=rb.find(b);
                if(it!=rb.end() && mx<=pos+3){ R.n=n; R.mode='R'; R.q=0; R.dir=1; R.lp=t.substr(0,pos); R.rp=""; R.keepR=it->second; return R; }
                if(rend && b>=rbmax){ bool z=true; for(long i=pos+4;i<(long)t.size();i++) if(t[i]=='1'){z=false;break;}
                    if(z){ R.n=n; R.mode='R'; R.q=0; R.dir=1; R.lp=t.substr(0,pos); R.rp=""; R.keepR=rbv.size(); return R; } }
            }
        }
        if(n>maxn){ R.toolong=true; return R; }
    }
}
// ---------------------------------------------------------------- engine
struct Engine {
    vector<Tok> L, R; char mode='X'; int q=0; int dir=1; i128 steps=0; bool halted=false;
    ll ngrow=0, nraw=0, nrule=0, nfast=0, nparam=0, nparamfail=0, nbig=0; bool useblocks=getenv("NOBLK")==nullptr;
    unordered_map<string,RawRes> cache;
    uint64_t evh=1469598103934665603ULL; ll nev=0;
    inline void mix(uint64_t x){ evh=(evh^x)*1099511628211ULL; evh^=evh>>31; nev++; }
    // parametric rules
    struct OutT { char k; string w; ll c0; vector<ll> a; };
    struct PRule { bool ok=false; vector<OutT> lo, ro; int keepR, keepL; char mode; int q, dir; i128 s0; vector<i128> sa;
        vector<Tok> lt, rt; vector<pair<int,int>> P; vector<ll> base; bool lend=false, rend=false; char mode0='X'; int q0=0, dir0=1; ll uses=0; };
    unordered_map<string,PRule> pcache;
    static const ll BIG=12;
    // ---- pushing with merging
    void pushR_digit(ll n){
        if(!R.empty() && R.back().k==KG){ Seg& g=pool[R.back().g]; g.ds.push_front(n); g.sm+=n; }
        else if(!R.empty() && R.back().k==KD){ ll m=R.back().n; R.pop_back(); int i=newseg(); pool[i].ds.set2(n,m); pool[i].sm=n+m; R.push_back({KG,0,"",i}); }
        else R.push_back(TD(n));
    }
    void pushL_digit(ll n){
        if(!L.empty() && L.back().k==KG){ Seg& g=pool[L.back().g]; g.ds.push_back(n); g.sm+=n; }
        else if(!L.empty() && L.back().k==KS){ ll m=L.back().n; L.pop_back(); int i=newseg(); pool[i].ds.set2(m,n); pool[i].sm=n+m; L.push_back({KG,0,"",i}); }
        else L.push_back(TS(n));
    }
    void pushR_seg(int gi){
        Seg& g=pool[gi];
        if(!R.empty() && R.back().k==KG){ int hi=R.back().g; Seg& h=pool[hi];
            if(h.ds.nruns()>=g.ds.nruns()){ h.ds.prependLeft(g.ds); h.sm+=g.sm; delseg(gi); }
            else { g.ds.appendRight(h.ds); g.sm+=h.sm; delseg(hi); R.back().g=gi; } }
        else if(!R.empty() && R.back().k==KD){ ll m=R.back().n; R.pop_back(); g.ds.push_back(m); g.sm+=m; R.push_back({KG,0,"",gi}); }
        else R.push_back({KG,0,"",gi});
    }
    void pushL_seg(int gi){
        Seg& g=pool[gi];
        if(!L.empty() && L.back().k==KG){ int hi=L.back().g; Seg& h=pool[hi];
            if(h.ds.nruns()>=g.ds.nruns()){ h.ds.appendRight(g.ds); h.sm+=g.sm; delseg(gi); }
            else { g.ds.prependLeft(h.ds); g.sm+=h.sm; delseg(hi); L.back().g=gi; } }
        else if(!L.empty() && L.back().k==KS){ ll m=L.back().n; L.pop_back(); g.ds.push_front(m); g.sm+=m; L.push_back({KG,0,"",gi}); }
        else L.push_back({KG,0,"",gi});
    }
    void pushR_tok(const Tok& t){ if(t.k==KD) pushR_digit(t.n); else if(t.k==KG) pushR_seg(t.g);
        else if(t.k==KK && !R.empty() && R.back().k==KK && R.back().g==t.g) R.back().n+=t.n;
        else if(t.k==KB && !R.empty() && R.back().k==KB){ R.back().w = t.w + R.back().w; } else R.push_back(t); }
    void pushL_tok(const Tok& t){ if(t.k==KS) pushL_digit(t.n); else if(t.k==KG) pushL_seg(t.g);
        else if(t.k==KK && !L.empty() && L.back().k==KK && L.back().g==t.g) L.back().n+=t.n;
        else if(t.k==KB && !L.empty() && L.back().k==KB){ L.back().w += t.w; } else L.push_back(t); }
    // unpack one period of the block at stack index idx (the period nearest the head); returns number of items inserted
    int unpack(vector<Tok>& st, bool left, long idx){
        Tok b=st[idx]; const vector<Tok>& per=bpool[b.g].per;
        vector<Tok> ins;
        if(left){ for(auto&t:per) ins.push_back(t); } else { for(long i=per.size()-1;i>=0;i--) ins.push_back(per[i]); }
        if(b.n>1){ st[idx].n--; st.insert(st.begin()+idx+1, ins.begin(), ins.end()); return ins.size(); }
        st.erase(st.begin()+idx); st.insert(st.begin()+idx, ins.begin(), ins.end()); return (int)ins.size()-1;
    }
    // peel: the W items nearest the head on stack st are made non-segments, non-blocks
    void peel(vector<Tok>& st, bool left, int W){
        int cnt=0; long idx=(long)st.size()-1;
        while(cnt<W && idx>=0){
            if(st[idx].k==KK){ int k=unpack(st,left,idx); idx+=k; continue; }
            if(st[idx].k==KG){
                int gi=st[idx].g; Seg& g=pool[gi]; ll n;
                if(left){ n=g.ds.back(); g.ds.pop_back(); } else { n=g.ds.front(); g.ds.pop_front(); }
                g.sm-=n; Tok d = left? TS(n) : TD(n);
                if(g.ds.empty()){ delseg(gi); st[idx]=d; }
                else { st.insert(st.begin()+idx+1, d); idx++; }
            }
            cnt++; idx--;
        }
    }
    // ---- blocks: tidy (form repeated item sequences into blocks) and crossing rules
    static bool simpleTok(const Tok& t){ return t.k!=KK && !(t.k==KG && pool[t.g].ds.size()>6) && !((t.k==KD||t.k==KS||t.k==KU) && t.n>BIG); }
    static void expandTok(const Tok& t, bool left, vector<Tok>& out){
        if(t.k==KG){ for(ll x: pool[t.g].ds.digits()) out.push_back(left? TS(x):TD(x)); } else out.push_back(t);
    }
    // per in tape order for items st[a..b) (stack indices); for R stacks the tape order is reversed
    vector<Tok> perOf(const vector<Tok>& st, bool left, long a, long b){
        vector<Tok> v; if(left){ for(long i=a;i<b;i++) expandTok(st[i],true,v); } else { for(long i=b-1;i>=a;i--) expandTok(st[i],false,v); } return v;
    }
    static string pkey(const vector<Tok>& v){ string k; for(auto&t:v){ k+=tstr(t); k+=' '; } return k; }
    ll nblk=0;
    void tidy(vector<Tok>& st, bool left){
        bool ch=true;
        while(ch){
            ch=false; long n=st.size();
            for(int p=1;p<=6 && !ch;p++){
                if(n<p+1) break;
                bool simple=true; for(long i=n-p;i<n;i++) if(!simpleTok(st[i])) { simple=false; break; }
                if(!simple) continue;
                vector<Tok> top=perOf(st,left,n-p,n); string kt=pkey(top);
                if(top.size()>12) continue;
                // case B: below is a block with the same period
                if(st[n-p-1].k==KK && pkey(bpool[st[n-p-1].g].per)==kt){ st.resize(n-p); st.back().n+=1; ch=true; nblk++; break; }
                // case A: two equal halves
                if(n>=2*p){
                    bool s2=true; for(long i=n-2*p;i<n-p;i++) if(!simpleTok(st[i])) { s2=false; break; }
                    if(!s2) continue;
                    vector<Tok> low=perOf(st,left,n-2*p,n-p);
                    if(pkey(low)==kt){
                        bool any=false; for(auto&t:top) if(t.k==KB||t.k==KU) any=true;
                        if(!any) continue;   // pure digit runs stay segments
                        for(long i=n-2*p;i<n;i++) if(st[i].k==KG) delseg(st[i].g);
                        st.resize(n-2*p); int bi=internBlk(top,left);
                        Tok bt{KK,2,"",bi};
                        if(!st.empty() && st.back().k==KK && st.back().g==bi) st.back().n+=2; else st.push_back(bt);
                        ch=true; nblk++; break;
                    }
                }
            }
        }
    }
    struct Cross { bool ok=false; int to=-1; ll st=0; };
    unordered_map<int,Cross> crossRc, crossLc;
    Cross& crossR(int bi){
        auto it=crossRc.find(bi); if(it!=crossRc.end()) return it->second;
        Cross c; string pb=bpool[bi].bits; string t="0100"+pb; long pos=0; int qq=0; ll n=0; long len=pb.size(); bool ok=false;
        while(n<1000000){
            if(pos<0 || pos>=(long)t.size()) break;
            int cc=t[pos]-'0'; if(qq==3 && cc==0 && pos>0 && t[pos-1]=='1') break;
            t[pos]='0'+TW[qq][cc]; int d=TM[qq][cc]; qq=TQ[qq][cc]; pos+=d; n++;
            if(qq==0 && pos==len && t.compare(len,4,"0100")==0){ ok=true; break; }
        }
        if(ok){ vector<Tok> lo=parse_left(t.substr(0,len)); bool good=true; for(auto&x:lo) if(x.k==KU && x.n>BIG) good=false;
            if(good){ c.ok=true; c.to=internBlk(lo,true); c.st=n; } }
        return crossRc[bi]=c;
    }
    Cross& crossL(int bi){
        auto it=crossLc.find(bi); if(it!=crossLc.end()) return it->second;
        Cross c; string pb=bpool[bi].bits; long len=pb.size(); string t=pb+"1"; long pos=len-1; int qq=1; ll n=0; bool ok=false;
        while(n<1000000){
            if(pos<0){ if(qq==1 && t[0]=='1') ok=true; break; }
            if(pos>=(long)t.size()) break;
            int cc=t[pos]-'0'; if(qq==3 && cc==0 && pos>0 && t[pos-1]=='1') break;
            t[pos]='0'+TW[qq][cc]; int d=TM[qq][cc]; qq=TQ[qq][cc]; pos+=d; n++;
        }
        if(ok){ vector<Tok> ro=parse_right(t.substr(1)); bool good=true; for(auto&x:ro) if(x.k==KU && x.n>BIG) good=false;
            if(good){ c.ok=true; c.to=internBlk(ro,false); c.st=n; } }
        return crossLc[bi]=c;
    }
    // ---- raw step
    static bool bigtok(const Tok& t){ return (t.k==KD||t.k==KS||t.k==KU) && t.n>BIG; }
    void raw(){
        int W=2;
        while(true){
            peel(L,true,W); peel(R,false,W);
            int nl=min((int)L.size(),W), nr=min((int)R.size(),W);
            vector<Tok> lt(L.end()-nl, L.end()); vector<Tok> rt; for(int i=0;i<nr;i++) rt.push_back(R[R.size()-1-i]);
            bool lend = nl==(int)L.size(), rend = nr==(int)R.size();
            bool big=false; for(auto&t:lt) if(bigtok(t)) big=true; for(auto&t:rt) if(bigtok(t)) big=true;
            bool ok = big? rawParam(lt,rt,lend,rend) : rawExact(lt,rt,lend,rend);
            if(ok) return;
            if(halted) return;
            W*=2;
            if(W>64){ fprintf(stderr,"window too large\n"); exit(2); }
        }
    }
    string midbits(char m){ return m=='R'?"0100": m=='L'?"1": m=='J'?"100":""; }
    long startpos(long lblen, char m){ if(m=='R') return lblen; if(m=='L'||m=='J') return lblen-1; return lblen-(dir<0?1:0); }
    int startq(char m){ return m=='R'?0: m=='L'?1: m=='J'?2: q; }
    // simulate exact bits for window tokens; returns false if the window must grow
    bool simWindow(const vector<Tok>& lt, const vector<Tok>& rt, bool lend, bool rend, RawRes& res, ll maxn){
        string lb; vector<long> lbv; for(auto&t:lt){ lb+=tbits(t,true); lbv.push_back(lb.size()); }
        string mid=midbits(mode); string rb; vector<long> rbv; long x=lb.size()+mid.size();
        for(auto&t:rt){ string b=tbits(t,false); rb+=b; x+=b.size(); rbv.push_back(x); }
        if(getenv("BIGWIN") && lb.size()+rb.size()>1000000){ fprintf(stderr,"big window %zu+%zu at step %s:", lb.size(), rb.size(), i2s(steps).c_str()); for(auto&t:lt) fprintf(stderr," %s",tstr(t).c_str()); fprintf(stderr," |%c| ",mode); for(auto&t:rt) fprintf(stderr," %s",tstr(t).c_str()); fprintf(stderr,"\n"); }
        res=rawsim(lb+mid+rb, startpos(lb.size(),mode), startq(mode), lend, rend, rbv, lbv, maxn);
        return true;
    }
    string key(const vector<Tok>& lt, const vector<Tok>& rt, bool lend, bool rend, bool abstr){
        string k; k+=mode; k+=char('0'+(mode=='X'?q:9)); k+= (mode=='X'?(dir<0?'<':'>'):'.'); k+= lend?'[':'('; 
        for(auto&t:lt){ k+='|'; k+=t.k; if(t.k==KB) k+=t.w; else if(t.k==KU){ k+=t.w; k+=':'; }
            if(t.k!=KB){ if(abstr && t.n>BIG){ k+='#'; k+=to_string(t.n%6); } else k+=to_string(t.n); } }
        k+='^';
        for(auto&t:rt){ k+='|'; k+=t.k; if(t.k==KB) k+=t.w; else if(t.k==KU){ k+=t.w; k+=':'; }
            if(t.k!=KB){ if(abstr && t.n>BIG){ k+='#'; k+=to_string(t.n%6); } else k+=to_string(t.n); } }
        k+= rend?']':')';
        return k;
    }
    void applyRes(const vector<Tok>& lt, const vector<Tok>& rt, const vector<Tok>& lo, const vector<Tok>& ro, int keepR, int keepL, char m2, int q2, int d2, bool lend, bool rend){
        int nl=lt.size(), nr=rt.size();
        L.resize(L.size()-nl); R.resize(R.size()-nr);
        if(keepR<0) keepR=nr;
        // left: kept window tokens then new tokens
        for(int i=0;i<keepL;i++) pushL_tok(lt[i]);
        vector<Tok> lo2=lo;
        if(lend && L.empty()){ // strip leading zeros at the left end of the tape
            while(!lo2.empty()){ Tok& t=lo2.front(); if(t.k==KB){ size_t a=t.w.find_first_not_of('0'); if(a==string::npos){ lo2.erase(lo2.begin()); continue; } t.w=t.w.substr(a); break; }
                else if(t.k==KU && t.w=="0"){ lo2.erase(lo2.begin()); continue; } else break; }
        }
        for(auto&t:lo2) pushL_tok(t);
        vector<Tok> ro2=ro;
        // right: kept window tokens (beyond), then new tokens, pushed from far to near
        for(int i=nr-1;i>=keepR;i--) pushR_tok(rt[i]);
        if(rend && keepR>=nr && R.empty()){
            while(!ro2.empty()){ Tok& t=ro2.back(); if(t.k==KB){ size_t b=t.w.find_last_not_of('0'); if(b==string::npos){ ro2.pop_back(); continue; } t.w=t.w.substr(0,b+1); break; }
                else if(t.k==KU && t.w=="0"){ ro2.pop_back(); continue; } else break; }
        }
        for(int i=(int)ro2.size()-1;i>=0;i--) pushR_tok(ro2[i]);
        mode=m2; q=q2; dir=d2;
        if(useblocks){ tidy(L,true); tidy(R,false); }
    }
    unordered_map<string,ll> hist; bool dohist=false;
    bool rawExact(const vector<Tok>& lt, const vector<Tok>& rt, bool lend, bool rend){
        string k=key(lt,rt,lend,rend,false);
        if(dohist) hist[key(lt,rt,lend,rend,true)]++;
        mix(std::hash<string>()(k));
        auto it=cache.find(k); RawRes res;
        if(it!=cache.end()) res=it->second;
        else { simWindow(lt,rt,lend,rend,res,(ll)5e6); if(res.grow){ ngrow++; return false; } if(res.toolong){ fprintf(stderr,"raw too long\n"); exit(2);} if(cache.size()>1000000) cache.clear(); cache[k]=res; }
        if(res.halt){ halted=true; steps+=res.n; return true; }
        vector<Tok> lo = res.lp.empty()? vector<Tok>() : parse_left(res.lp);
        vector<Tok> ro = res.rp.empty()? vector<Tok>() : parse_right(res.rp);
        if(res.keepL>0) lo.clear();
        applyRes(lt,rt,lo,ro,res.keepR,res.keepL,res.mode,res.q,res.dir,lend,rend);
        steps+=res.n; nraw++;
        return true;
    }
    // parametric: big parameters replaced by probe values; affine fit
    bool rawParam(const vector<Tok>& lt, const vector<Tok>& rt, bool lend, bool rend){
        string k=key(lt,rt,lend,rend,true);
        if(dohist) hist[k]++;
        mix(std::hash<string>()(k)^0x9e3779b97f4a7c15ULL);
        vector<ll*> dummy;
        vector<pair<int,int>> P; // (side 0=L/1=R, index)
        for(int i=0;i<(int)lt.size();i++) if(bigtok(lt[i])) P.push_back({0,i});
        for(int i=0;i<(int)rt.size();i++) if(bigtok(rt[i])) P.push_back({1,i});
        int np=P.size();
        vector<ll> base(np), xs(np);
        for(int j=0;j<np;j++){ ll v = P[j].first==0? lt[P[j].second].n : rt[P[j].second].n; xs[j]=v; base[j]=BIG+1+((v-(BIG+1))%6+6)%6; }
        auto it=pcache.find(k);
        if(it==pcache.end()){
            PRule pr=learnParam(lt,rt,lend,rend,P,base);
            pr.lt=lt; pr.rt=rt; pr.P=P; pr.base=base; pr.lend=lend; pr.rend=rend; pr.mode0=mode; pr.q0=q; pr.dir0=dir;
            for(int j=0;j<np;j++){ if(P[j].first==0) pr.lt[P[j].second].n=base[j]; else pr.rt[P[j].second].n=base[j]; }
            if(pcache.size()>2000000) pcache.clear();
            it=pcache.emplace(k,pr).first;
        }
        PRule& pr=it->second; pr.uses++;
        if(!pr.ok){ nparamfail++; return bigExact(lt,rt,lend,rend); }
        vector<ll> tj(np); for(int j=0;j<np;j++) tj[j]=(xs[j]-base[j])/6;
        auto mk=[&](const vector<OutT>& v){ vector<Tok> o; for(auto& x: v){ i128 val=x.c0; for(int j=0;j<np;j++) val+=(i128)x.a[j]*tj[j];
            Tok t; t.k=x.k; t.w=x.w; t.n=(ll)val; t.g=-1; if(t.k!=KB && val<0){ fprintf(stderr,"negative param\n"); exit(3);} o.push_back(t);} return o; };
        vector<Tok> lo=mk(pr.lo), ro=mk(pr.ro);
        i128 st=pr.s0; for(int j=0;j<np;j++) st+=pr.sa[j]*tj[j];
        applyRes(lt,rt,lo,ro,pr.keepR,pr.keepL,pr.mode,pr.q,pr.dir,lend,rend);
        steps+=st; nparam++;
        return true;
    }
    struct Probe { RawRes r; vector<Tok> lo, ro; };
    Probe probe(const vector<Tok>& lt, const vector<Tok>& rt, bool lend, bool rend, const vector<pair<int,int>>& P, const vector<ll>& vals){
        vector<Tok> l2=lt, r2=rt;
        for(size_t j=0;j<P.size();j++){ if(P[j].first==0) l2[P[j].second].n=vals[j]; else r2[P[j].second].n=vals[j]; }
        Probe p; simWindow(l2,r2,lend,rend,p.r,(ll)2e6);
        if(!p.r.halt && !p.r.toolong){ p.lo = p.r.lp.empty()? vector<Tok>() : parse_left(p.r.lp); p.ro = p.r.rp.empty()? vector<Tok>() : parse_right(p.r.rp); if(p.r.keepL>0) p.lo.clear(); }
        return p;
    }
    static bool sameShape(const vector<Tok>& a, const vector<Tok>& b){
        if(a.size()!=b.size()) return false;
        for(size_t i=0;i<a.size();i++){ if(a[i].k!=b[i].k || a[i].w!=b[i].w) return false; }
        return true;
    }
    PRule learnParam(const vector<Tok>& lt, const vector<Tok>& rt, bool lend, bool rend, const vector<pair<int,int>>& P, const vector<ll>& base){
        PRule pr; int np=P.size();
        vector<Probe> pv; vector<vector<ll>> vals;
        vals.push_back(base);
        for(int j=0;j<np;j++){ auto v=base; v[j]+=6; vals.push_back(v); }
        { auto v=base; for(auto&x:v) x+=6; vals.push_back(v); }
        { auto v=base; for(auto&x:v) x+=12; vals.push_back(v); }
        { auto v=base; for(int j=0;j<np;j++) v[j]+=6*(j+1)+6; vals.push_back(v); }
        for(auto& v: vals){ pv.push_back(probe(lt,rt,lend,rend,P,v)); if(pv.back().r.halt || pv.back().r.toolong || pv.back().r.grow) return pr; }
        const Probe& b=pv[0];
        for(auto& p: pv){ if(p.r.mode!=b.r.mode || p.r.q!=b.r.q || p.r.dir!=b.r.dir || p.r.keepR!=b.r.keepR || p.r.keepL!=b.r.keepL) return pr;
            if(!sameShape(p.lo,b.lo) || !sameShape(p.ro,b.ro)) return pr; }
        auto fit=[&](const vector<Tok>& bv, int side, vector<OutT>& out)->bool{
            for(size_t i=0;i<bv.size();i++){
                OutT o; o.k=bv[i].k; o.w=bv[i].w; o.c0=bv[i].n; o.a.assign(np,0);
                for(int j=0;j<np;j++){ const vector<Tok>& v = side==0? pv[1+j].lo : pv[1+j].ro; o.a[j]=v[i].n-o.c0; }
                for(size_t pi=np+1; pi<pv.size(); pi++){
                    const vector<Tok>& v = side==0? pv[pi].lo : pv[pi].ro;
                    i128 pred=o.c0; for(int j=0;j<np;j++) pred+=(i128)o.a[j]*((vals[pi][j]-base[j])/6);
                    if(pred!=(i128)v[i].n) return false;
                }
                out.push_back(o);
            }
            return true;
        };
        if(!fit(b.lo,0,pr.lo) || !fit(b.ro,1,pr.ro)) return pr;
        pr.s0=b.r.n; pr.sa.assign(np,0);
        for(int j=0;j<np;j++) pr.sa[j]=pv[1+j].r.n-b.r.n;
        for(size_t pi=np+1; pi<pv.size(); pi++){ i128 pred=pr.s0; for(int j=0;j<np;j++) pred+=pr.sa[j]*((vals[pi][j]-base[j])/6); if(pred!=(i128)pv[pi].r.n) return PRule(); }
        pr.keepR=b.r.keepR; pr.keepL=b.r.keepL; pr.mode=b.r.mode; pr.q=b.r.q; pr.dir=b.r.dir; pr.ok=true;
        return pr;
    }
    bool bigExact(const vector<Tok>& lt, const vector<Tok>& rt, bool lend, bool rend){
        RawRes res; simWindow(lt,rt,lend,rend,res,(ll)2e8); nbig++;
        if(res.grow){ ngrow++; return false; }
        if(res.toolong){ fprintf(stderr,"big raw too long\n"); exit(2); }
        if(res.halt){ halted=true; steps+=res.n; return true; }
        vector<Tok> lo = res.lp.empty()? vector<Tok>() : parse_left(res.lp);
        vector<Tok> ro = res.rp.empty()? vector<Tok>() : parse_right(res.rp);
        if(res.keepL>0) lo.clear();
        applyRes(lt,rt,lo,ro,res.keepR,res.keepL,res.mode,res.q,res.dir,lend,rend);
        steps+=res.n; nraw++;
        return true;
    }
    // ---- cycle detection at far-pass starts (R mode facing a big segment) and affine extrapolation
    bool cycles=getenv("NOCYC")==nullptr;
    struct PLoc { int kind; long idx; int seg; long ri; bool back; bool resid; };   // kind 0: L tok, 1: R tok, 2: seg run count
    struct Samp { uint64_t sig; vector<i128> vals; i128 steps; uint64_t ev; ll nev; };
    deque<Samp> hist2; ll sampIdx=0; unordered_map<uint64_t, deque<ll>> occ;
    ll njump=0, ncycjumped=0; i128 jumpsteps=0; ll nsamp=0, nsampskip=0;
    static const ll RUNBIG=64;
    bool sigTok(const Tok& t, int kind, long idx, string& s, vector<PLoc>& locs, vector<i128>& vals){
        switch(t.k){
            case KD: case KS: case KU:
                s+=t.k; s+=t.w; if(t.n>BIG){ s+='#'; s+=char('0'+t.n%6); locs.push_back({kind,idx,-1,0,false,true}); vals.push_back(t.n); } else s+=to_string(t.n); break;
            case KB: s+='b'; s+=t.w; break;
            case KK: s+='K'; s+=to_string(t.g); if(t.n>BIG){ s+='#'; locs.push_back({kind,idx,-1,0,false,false}); vals.push_back(t.n); } else { s+=':'; s+=to_string(t.n);} break;
            case KG: {
                RunDeque& d=pool[t.g].ds; s+="G["; for(ll x:d.fb){ s+=to_string(x); s+=','; } s+='|';
                long nr=d.nruns(); long a = nr<=16? nr : 12; long b = nr<=16? nr : nr-4;
                auto runsig=[&](long i, bool fromBack){ const Run r=d.run(i); s+='('; for(ll x:r.pat){ s+=to_string(x); s+=','; } s+=')';
                    if(r.c>RUNBIG){ s+='#'; locs.push_back({2,idx,t.g, fromBack? nr-1-i : i, fromBack,false}); vals.push_back(r.c); } else s+=to_string(r.c); };
                for(long i=0;i<a;i++) runsig(i,false);
                if(b>a){ i128 cn=d.n, sm=pool[t.g].sm; for(ll x:d.fb){ cn--; sm-=x; } for(ll x:d.bb){ cn--; sm-=x; }
                    for(long i=0;i<a;i++){ const Run r=d.run(i); ll ps=0; for(ll x:r.pat) ps+=x; cn-=(i128)r.c*r.pat.size(); sm-=(i128)r.c*ps; }
                    for(long i=b;i<nr;i++){ const Run r=d.run(i); ll ps=0; for(ll x:r.pat) ps+=x; cn-=(i128)r.c*r.pat.size(); sm-=(i128)r.c*ps; }
                    s+="{int "+i2s(cn)+" "+i2s(sm)+" "+to_string(b-a)+"}"; }
                for(long i=b;i<nr;i++) runsig(i,true);
                s+='|'; for(ll x:d.bb){ s+=to_string(x); s+=','; } s+=']';
                break; }
        }
        s+=' '; return true;
    }
    bool sample(){
        nsamp++;
        if(L.size()+R.size()>80){ nsampskip++; return false; }
        string s; s+=mode; vector<PLoc> locs; vector<i128> vals;
        for(long i=0;i<(long)L.size();i++) if(!sigTok(L[i],0,i,s,locs,vals)) return false;
        s+="||";
        for(long i=(long)R.size()-1;i>=0;i--) if(!sigTok(R[i],1,i,s,locs,vals)) return false;
        uint64_t sh=std::hash<string>()(s);
        Samp cur{sh, vals, steps, evh, nev};
        evh=1469598103934665603ULL;
        ll i=sampIdx++;
        hist2.push_back(cur); if(hist2.size()>6000) hist2.pop_front();
        ll base=i-(ll)hist2.size()+1;   // index of hist2[0]
        auto H=[&](ll j)->Samp&{ return hist2[j-base]; };
        auto& oc=occ[sh];
        bool jumped=false;
        if(!oc.empty()){
            ll j1=oc.back(); ll P=i-j1;
            if(j1-3*P+3*P==j1 && i-3*P>=base && P<=1500){
                ll j2=i-2*P, j3=i-3*P;
                bool ok = H(j2).sig==sh && H(j3).sig==sh && H(j1).vals.size()==vals.size() && H(j2).vals.size()==vals.size() && H(j3).vals.size()==vals.size();
                // identical per-pass signatures and event hashes over the last three periods
                for(ll t=i; ok && t>j3+P; t--){ if(H(t).sig!=H(t-P).sig || H(t).ev!=H(t-P).ev) ok=false; }
                vector<i128> D(vals.size());
                for(size_t p=0; ok && p<vals.size(); p++){
                    i128 d1=vals[p]-H(j1).vals[p], d2=H(j1).vals[p]-H(j2).vals[p], d3=H(j2).vals[p]-H(j3).vals[p];
                    if(d1!=d2 || d2!=d3) ok=false; D[p]=d1;
                    if(locs[p].resid && d1%6!=0) ok=false;
                }
                i128 C1=H(j2).steps-H(j3).steps, C2=H(j1).steps-H(j2).steps, C3=steps-H(j1).steps;
                if(ok && C3-C2!=C2-C1) ok=false;
                if(ok){
                    i128 dl=C3-C2;
                    // number of further cycles
                    i128 k=(i128)1<<100;
                    for(size_t p=0;p<vals.size();p++) if(D[p]<0){ i128 ad=-D[p]; i128 thr=(locs[p].kind==2? RUNBIG : BIG) + 4*ad + 64; if(vals[p]<thr) k=0; else k=min(k,(vals[p]-thr)/ad); }
                    if(k>=(i128)1<<99) k=0;   // nothing decreases: leave it to the plain engine (would run forever)
                    if(k>0){
                        for(size_t p=0;p<vals.size();p++){ if(D[p]==0) continue; i128 nv=vals[p]+k*D[p];
                            const PLoc& lc=locs[p];
                            if(lc.kind==0) L[lc.idx].n=(ll)nv; else if(lc.kind==1) R[lc.idx].n=(ll)nv;
                            else { Seg& g=pool[lc.seg]; RunDeque& d=g.ds; size_t ix = lc.back? d.nruns()-1-lc.ri : lc.ri; Run r=d.run(ix);
                                i128 dc=nv-r.c; ll ps=0; for(ll x:r.pat) ps+=x; g.sm+=dc*ps; d.n+=(ll)(dc*(i128)r.pat.size()); d.cnt(ix)=(ll)nv; }
                        }
                        i128 add=k*C3 + dl*(k*(k+1)/2);
                        steps+=add; jumpsteps+=add; njump++; ncycjumped+=(ll)k; jumped=true;
                        hist2.clear(); occ.clear(); sampIdx=0;
                    }
                }
            }
        }
        if(!jumped){ oc.push_back(i); if(oc.size()>8) oc.pop_front(); }
        if(occ.size()>200000){ occ.clear(); }
        return false;
    }
    // ---- one engine step
    void step(){
        if(cycles && mode=='R' && !R.empty() && R.back().k==KG && pool[R.back().g].ds.size()>=1000){ if(sample()) return; }
        mix((uint64_t)mode*131 + (R.empty()?7:R.back().k) + 977*(L.empty()?7:L.back().k));
        if(mode=='R' && !R.empty()){
            Tok& t=R.back();
            if(t.k==KG){ int gi=t.g; R.pop_back(); Seg& g=pool[gi]; steps+=6*g.sm+3*(i128)g.ds.size(); pushL_seg(gi); nfast++; return; }
            if(t.k==KD){ ll n=t.n; R.pop_back(); steps+=6*(i128)n+3; pushL_digit(n); nrule++; return; }
            if(t.k==KK){ Cross& c=crossR(t.g); if(c.ok){ ll cnt=t.n; R.pop_back(); steps+=(i128)c.st*cnt; pushL_tok(Tok{KK,cnt,"",c.to}); nfast++; return; }
                unpack(R,false,R.size()-1); return; }
        } else if((mode=='L'||mode=='J') && !L.empty()){
            Tok& t=L.back();
            if(mode=='L'){
                if(t.k==KG){ int gi=t.g; L.pop_back(); Seg& g=pool[gi]; steps+=2*g.sm+5*(i128)g.ds.size(); pushR_seg(gi); nfast++; return; }
                if(t.k==KS){ ll n=t.n; L.pop_back(); steps+=2*(i128)n+5; pushR_digit(n); nrule++; return; }
                if(t.k==KK){ Cross& c=crossL(t.g); if(c.ok){ ll cnt=t.n; L.pop_back(); steps+=(i128)c.st*cnt; pushR_tok(Tok{KK,cnt,"",c.to}); nfast++; return; }
                    unpack(L,true,L.size()-1); return; }
            } else {
                if(t.k==KG){ int gi=t.g; Seg& g=pool[gi]; ll n=g.ds.back(); g.ds.pop_back(); g.sm-=n; if(g.ds.empty()){ L.pop_back(); delseg(gi);} steps+=2*(i128)n+3; pushR_digit(n+1); mode='L'; nrule++; return; }
                if(t.k==KS){ ll n=t.n; L.pop_back(); steps+=2*(i128)n+3; pushR_digit(n+1); mode='L'; nrule++; return; }
                if(t.k==KK){ unpack(L,true,L.size()-1); return; }
            }
        }
        raw();
    }
    string tape(long& head, char& st){
        string lb; for(auto&t:L) lb+=tbits(t,true);
        string rb; for(long i=R.size()-1;i>=0;i--) rb+=tbits(R[i],false);
        if(mode=='R'){ head=lb.size(); st='A'; return lb+"0100"+rb; }
        if(mode=='L'){ head=(long)lb.size()-1; st='B'; return lb+"1"+rb; }
        if(mode=='J'){ head=(long)lb.size()-1; st='C'; return lb+"100"+rb; }
        head=(long)lb.size()-(dir<0?1:0); st='A'+q; return lb+rb;
    }
    string show(int k){
        string s; int nl=L.size(); for(int i=max(0,nl-k);i<nl;i++){ s+=tstr(L[i]); s+=' '; }
        s+= string("[")+mode+(mode=='X'?string(1,'A'+q):string(""))+"] ";
        int nr=R.size(); for(int i=nr-1;i>=max(0,nr-k);i--){ s+=tstr(R[i]); s+=' '; }
        return s;
    }
};
// direct simulation of G (for checking)
static string direct(ll N, long& head, char& st){
    vector<char> t(1<<22,0); long p=1<<21, lo=p, hi=p; int q=0;
    for(ll i=0;i<N;i++){ int c=t[p]; t[p]=TW[q][c]; p+=TM[q][c]; q=TQ[q][c]; lo=min(lo,p); hi=max(hi,p); }
    string s; for(long i=lo;i<=hi;i++) s+='0'+t[i]; head=p-lo; st='A'+q; return s;
}
static pair<string,long> norm(string x, long h){ long i=0; while(i<(long)x.size() && x[i]=='0' && i<h) i++; x=x.substr(i); h-=i; while(!x.empty() && x.back()=='0' && (long)x.size()-1>h) x.pop_back(); return {x,h}; }
int main(int argc, char** argv){
    MERGELIT = getenv("NOCYC")!=nullptr;   // merged literal blocks would make the cycle signatures long
    string cmd = argc>1? argv[1] : "run";
    if(cmd=="check"){
        for(int a=2;a<argc;a++){
            ll N=(ll)atof(argv[a]); Engine e; while(e.steps<N && !e.halted) e.step();
            long h1; char s1; string t1=e.tape(h1,s1); long h2; char s2; string t2=direct((ll)e.steps,h2,s2);
            auto A=norm(t1,h1), B=norm(t2,h2);
            printf("%s steps=%s match=%d raw=%lld rule=%lld fast=%lld param=%lld pfail=%lld\n", argv[a], i2s(e.steps).c_str(), (int)(A==B && s1==s2), e.nraw,e.nrule,e.nfast,e.nparam,e.nparamfail);
            if(!(A==B&&s1==s2)){ printf("tok %s\ndir %s\n", (A.first.substr(0,A.second)+"["+s1+"]"+A.first.substr(A.second)).substr(0,300).c_str(), (B.first.substr(0,B.second)+"["+s2+"]"+B.first.substr(B.second)).substr(0,300).c_str()); }
        }
        return 0;
    }
    if(cmd=="hist"){
        double a=atof(argv[2]), b=atof(argv[3]); Engine e; while((double)e.steps<a) e.step(); e.dohist=true; ll r0=e.nraw+e.nparam, f0=e.nfast+e.nrule;
        while((double)e.steps<b) e.step();
        vector<pair<ll,string>> v; for(auto&x:e.hist) v.push_back({x.second,x.first}); sort(v.rbegin(),v.rend());
        printf("raw+param %lld fast+rule %lld\n", e.nraw+e.nparam-r0, e.nfast+e.nrule-f0);
        for(int i=0;i<min((int)v.size(),40);i++) printf("%10lld %s\n", v[i].first, v[i].second.c_str());
        return 0;
    }
    if(cmd=="passes"){
        double a=atof(argv[2]); int M=atoi(argv[3]); Engine e; while((double)e.steps<a) e.step();
        int c=0; char pm=e.mode;
        while(c<M){ pm=e.mode; e.step(); if(e.mode=='R' && pm!='R' && e.L.size()<=5){ c++;
            string s; for(auto&t:e.L) s+=tstr(t)+" "; s+="|| ";
            for(long i=e.R.size()-1;i>=0;i--){ const Tok& t=e.R[i]; if(t.k==KG){ Seg& g=pool[t.g]; s+="G[n="+to_string(g.ds.size())+" sm="+i2s(g.sm)+" first="+to_string(g.ds.front())+" last="+to_string(g.ds.back())+"] "; } else s+=tstr(t)+" "; }
            printf("%s %s\n", i2s(e.steps).c_str(), s.c_str()); } }
        return 0;
    }
    if(cmd=="trace"){
        double a=atof(argv[2]); int M=atoi(argv[3]); Engine e; while((double)e.steps<a) e.step();
        for(int c=0;c<M;c++){ string before=e.show(6); i128 s0=e.steps; e.step(); printf("%s  %s  -> +%s\n", i2s(s0).c_str(), before.c_str(), i2s(e.steps-s0).c_str()); }
        return 0;
    }
    if(cmd=="ends"){
        double a=atof(argv[2]), b=atof(argv[3]); Engine e; while((double)e.steps<a) e.step();
        ll ends=0, ev=0; i128 last=e.steps; double tg=a;
        while((double)e.steps<b){ bool atend = e.mode=='R' && e.R.empty(); e.step(); ev++; if(atend) ends++;
            if((double)e.steps>=tg){ printf("%s ends=%lld events=%lld Lsize=%zu Rsize=%zu\n", i2s(e.steps).c_str(), ends, ev, e.L.size(), e.R.size()); tg*=1.2; } }
        return 0;
    }
    if(cmd=="dump"){
        double a=atof(argv[2]); Engine e; while((double)e.steps<a) e.step();
        printf("steps %s mode %c\nL:", i2s(e.steps).c_str(), e.mode);
        auto pr=[&](const Tok& t){ if(t.k==KG){ Seg& g=pool[t.g]; printf(" G{%zu:", g.ds.size()); int c=0; for(ll x: g.ds.digits()){ if(c<12||c>=(long)g.ds.size()-12) printf(" %lld",x); else if(c==12) printf(" ..."); c++; } printf("}"); } else printf(" %s", tstr(t).c_str()); };
        for(auto&t:e.L) pr(t); printf("\nR:"); for(long i=e.R.size()-1;i>=0;i--) pr(e.R[i]); printf("\n");
        return 0;
    }
    if(cmd=="zone"){
        // at each start of a far pass (R mode, about to cross the biggest segment), print left items and right items up to it
        double a=atof(argv[2]); int M=atoi(argv[3]); Engine e; while((double)e.steps<a) e.step();
        int c=0;
        while(c<M){
            e.step();
            if(e.mode=='R' && !e.R.empty() && e.R.back().k==KG && pool[e.R.back().g].ds.size()>100000){
                c++; string s; for(auto&t:e.L){ if(t.k==KG){ Seg&g=pool[t.g]; if(g.ds.size()>20){ s+="G["+to_string(g.ds.size())+"] "; continue;} s+="<"; for(ll x:g.ds.digits()) s+=to_string(x)+","; s.back()='>'; s+=" "; } else s+=tstr(t)+" "; }
                Seg& g=pool[e.R.back().g]; string r; int k=0; for(ll x: g.ds.digits()){ if(k++>=24) break; r+=to_string(x)+","; }
                i128 cnt=g.ds.size(); 
                printf("%s %s || MID n=%s sm=%s first: %s\n", i2s(e.steps).c_str(), s.c_str(), i2s(cnt).c_str(), i2s(g.sm).c_str(), r.c_str());
            }
        }
        return 0;
    }
    if(cmd=="cyc"){
        // fraction of far-pass starts whose left zone (L stack) + first 40 digits of MID repeat a signature seen within the last W passes
        double a=atof(argv[2]), b=atof(argv[3]); int Wn=atoi(argv[4]); Engine e; while((double)e.steps<a) e.step();
        unordered_map<string,ll> last; ll pass=0, rep=0; map<ll,ll> per;
        while((double)e.steps<b){
            e.step();
            if(e.mode=='R' && !e.R.empty() && e.R.back().k==KG && pool[e.R.back().g].ds.size()>50000){
                pass++; string s; for(auto&t:e.L){ if(t.k==KG){ for(ll x:pool[t.g].ds.digits()) s+=to_string(x)+","; s+="|"; } else s+=tstr(t)+" "; }
                s+="#"; int k=0; for(ll x: pool[e.R.back().g].ds.digits()){ if(k++>=40) break; s+=to_string(x)+","; }
                auto it=last.find(s); if(it!=last.end() && pass-it->second<=Wn){ rep++; per[pass-it->second]++; }
                last[s]=pass;
            }
        }
        printf("passes %lld repeats %lld\n", pass, rep); int c=0; vector<pair<ll,ll>> v; for(auto&x:per) v.push_back({x.second,x.first}); sort(v.rbegin(),v.rend()); for(auto&x:v){ if(c++>15) break; printf("  period %lld: %lld\n", x.second, x.first); }
        return 0;
    }
    if(cmd=="mid"){
        double a=atof(argv[2]); int M=atoi(argv[3]); int K=atoi(argv[4]); Engine e; while((double)e.steps<a) e.step();
        int c=0;
        while(c<M){ e.step();
            if(e.mode=='R' && !e.R.empty() && e.R.back().k==KG && pool[e.R.back().g].ds.size()>1000){ c++;
                string s; for(auto&t:e.L){ if(t.k==KG){ Seg&g=pool[t.g]; s+="<"; for(ll x:g.ds.digits()) s+=to_string(x)+","; s.back()='>'; s+=" "; } else s+=tstr(t)+" "; }
                RunDeque& d=pool[e.R.back().g].ds; string r="fb["; for(ll x:d.fb) r+=to_string(x)+","; r+="] ";
                int k=0; for(size_t ui=0; ui<d.nruns(); ui++){ Run u=d.run(ui); if(k++>=K) break; r+="("; for(ll x:u.pat) r+=to_string(x)+","; r.back()=')'; r+="^"+to_string(u.c)+" "; }
                r+=" ... runs="+to_string(d.nruns())+" ... ";
                k=0; for(long i=max(0L,(long)d.nruns()-3);i<(long)d.nruns();i++){ Run u=d.run(i); r+="("; for(ll x:u.pat) r+=to_string(x)+","; r.back()=')'; r+="^"+to_string(u.c)+" "; }
                r+="bb["; for(ll x:d.bb) r+=to_string(x)+","; r+="]";
                string rest; for(long i=(long)e.R.size()-2;i>=0;i--) rest+=tstr(e.R[i])+" ";
                printf("%s %s || %s || %s\n", i2s(e.steps).c_str(), s.c_str(), r.c_str(), rest.c_str()); } }
        return 0;
    }
    if(cmd=="export"){
        double a=atof(argv[2]); Engine e; double tgt=1e10; auto t0=chrono::steady_clock::now();
        while((double)e.steps<a && !e.halted){ e.step();
            if((double)e.steps>=tgt){ while((double)e.steps>=tgt) tgt*=10; { size_t nr=0, nd=0; for(auto& g: pool.v) if(g){ nr+=g->ds.nruns(); nd+=g->ds.pd.size(); }
                printf("t=%.0fs steps=%s param=%lld grow=%lld jumps=%lld pcache=%zu cache=%zu segs=%zu free=%zu runs=%zu rundigits=%zu L=%zu R=%zu\n", chrono::duration<double>(chrono::steady_clock::now()-t0).count(), i2s(e.steps).c_str(), e.nparam, e.ngrow, e.njump, e.pcache.size(), e.cache.size(), pool.size(), freelist.size(), nr, nd, e.L.size(), e.R.size()); } fflush(stdout); } }
        if(e.halted) printf("HALT at step %s\n", i2s(e.steps).c_str());
        FILE* f=fopen(argv[3],"w");
        auto tk=[&](const Tok& t){ string s; s+=t.k; s+=' '; s+=to_string(t.n); s+=' '; s+= t.w.empty()? "-" : t.w; return s; };
        for(auto& kv: e.pcache){ auto& p=kv.second; if(!p.ok) continue;
            fprintf(f,"RULE %lld %c %d %d %d %d np=%zu\n", p.uses, p.mode0, p.q0, p.dir0, (int)p.lend, (int)p.rend, p.P.size());
            fprintf(f,"P"); for(auto& x: p.P) fprintf(f," %d:%d",x.first,x.second); fprintf(f,"\n");
            fprintf(f,"LT %zu\n",p.lt.size()); for(auto& t: p.lt) fprintf(f,"%s\n",tk(t).c_str());
            fprintf(f,"RT %zu\n",p.rt.size()); for(auto& t: p.rt) fprintf(f,"%s\n",tk(t).c_str());
            auto ot=[&](const char* nm, const vector<Engine::OutT>& v){ fprintf(f,"%s %zu\n",nm,v.size()); for(auto& o: v){ fprintf(f,"%c %lld %s",o.k,o.c0,o.w.empty()?"-":o.w.c_str()); for(auto x:o.a) fprintf(f," %lld",x); fprintf(f,"\n"); } };
            ot("LO",p.lo); ot("RO",p.ro);
            fprintf(f,"END %c %d %d %d %d %s",p.mode,p.q,p.dir,p.keepL,p.keepR,i2s(p.s0).c_str()); for(auto x:p.sa) fprintf(f," %s",i2s(x).c_str()); fprintf(f,"\n");
        }
        fclose(f); printf("steps=%s pcache=%zu\n", i2s(e.steps).c_str(), e.pcache.size()); return 0;
    }
    if(cmd=="run"){
        double secs = argc>2? atof(argv[2]) : 60;
        Engine e; auto t0=chrono::steady_clock::now(); double tgt=1e5;
        while(!e.halted){
            for(int i=0;i<1000000 && !e.halted;i++){ e.step(); }
            double el=chrono::duration<double>(chrono::steady_clock::now()-t0).count();
            if((double)e.steps>=tgt || el>secs){
                while((double)e.steps>=tgt) tgt*=10;
                long items=e.L.size()+e.R.size();
                printf("t=%.0fs steps=%s (%.3e) raw=%lld rule=%lld fast=%lld param=%lld pfail=%lld grow=%lld big=%lld blk=%lld jumps=%lld cyc=%lld samp=%lld items=%ld cache=%zu pcache=%zu\n", el, i2s(e.steps).c_str(), (double)e.steps, e.nraw,e.nrule,e.nfast,e.nparam,e.nparamfail,e.ngrow,e.nbig,e.nblk,e.njump,e.ncycjumped,e.nsamp,items,e.cache.size(),e.pcache.size());
                fflush(stdout);
                if(el>secs) break;
            }
        }
        if(e.halted) printf("HALT at step %s\n", i2s(e.steps).c_str());
        return 0;
    }
}
