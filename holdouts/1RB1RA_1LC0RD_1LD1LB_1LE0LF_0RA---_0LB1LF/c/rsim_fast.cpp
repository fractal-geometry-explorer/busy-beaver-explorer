// rsim_fast.cpp: a faster C++ port of holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim.py.
//
// Same algorithm, constants and order of decisions as rsim.py (and as the older port c/rsim.cpp in that folder), so
// its runs follow the same trajectory: on this machine both stop at the same step counts with the same numbers of
// rules, learning calls, samples and jumps. What is faster: rules are looked up by a running hash of the trailing
// cells instead of one string per lookback length, rules are passed by pointer, and the rope tidying compares words
// in place instead of building strings. On this machine that makes it about 15 to 25 times faster than rsim.py and
// about 1.75 times faster than c/rsim.cpp.
//
// Exactness: periodic and transition rules are exact (learned on a scratch tape, applied by induction on copies);
// sample-level jumps are validated, not proved (see the docstring of rsim.py). Counts and steps are 128-bit.
//
// Memory: the memo tables are cleared when they grow large, and runs stop (MEMORY limit reached) past MEMGB GiB.
//
// usage: rsim_fast MACHINE run SECONDS [JSON]   growing targets (x1.5; with DECADES set, the targets of rsim_screen.py:
//                                              1e6 .. 1e10, then x10) until the wall-clock budget, progress lines
//        rsim_fast MACHINE stats T1,T2,...      after run(Ti): steps, state, rules, learning calls, jumps, samples
//        rsim_fast MACHINE at T1,T2,...         after run(Ti): steps, state, head offset, whole tape (see py/rsim_fast_validate.py)
//        rsim_fast MACHINE items T1,T2,...      after run(Ti): the tape as items (word)^count
// env: KEEP (buffer cells, default 32), NOJUMP (turn sample-level jumps off), DECADES, MEMGB (default 5)
// build: g++ -O2 -std=c++17 -o rsim_fast rsim_fast.cpp
#include <bits/stdc++.h>
using namespace std;
typedef __int128 i128;
static string i2s(i128 x){ if(x==0) return "0"; bool neg=x<0; if(neg) x=-x; string s; while(x>0){ s+=char('0'+(int)(x%10)); x/=10;} if(neg) s+='-'; reverse(s.begin(),s.end()); return s; }
static double i2d(i128 x){ return (double)x; }
static i128 floordiv(i128 a, i128 b){ i128 q=a/b; if((a%b!=0) && ((a<0)!=(b<0))) q--; return q; }

struct Item { string w; i128 c; bool operator==(const Item&o) const { return c==o.c && w==o.w; } };
typedef vector<Item> Rope;

// ---------------------------------------------------------------- canon / compress
struct Canon { string W; int k; int r; };
static unordered_map<string,Canon> canon_memo;
static Canon canon(const string& w){
    auto it=canon_memo.find(w); if(it!=canon_memo.end()) return it->second;
    if(canon_memo.size()>1000000) canon_memo.clear();
    int n=w.size(); string root=w;
    for(int p=1;p<=n/2;p++){ if(n%p) continue; bool ok=true; for(int i=p;i<n;i++) if(w[i]!=w[i-p]){ok=false;break;} if(ok){ root=w.substr(0,p); break; } }
    int p=root.size(); string dd=root+root; int r=0; string best=dd.substr(0,p);
    for(int i=1;i<p;i++){ string c=dd.substr(i,p); if(c<best){best=c;r=i;} }
    Canon c{best, n/p, r};
    return canon_memo.emplace(w,c).first->second;
}
static bool sw(const string& s, const string& w, size_t pos){ return pos<=s.size() && s.compare(pos, w.size(), w)==0 && pos+w.size()<=s.size(); }
static vector<Item> compress1(const string& s, int minrep=3, int maxp=12, int mincover=6){
    vector<Item> out; long i=0, n=s.size(), loose=0;
    while(i<n){
        long bestcov=-1; int bp=0; long br=0;
        for(int p=1;p<=maxp;p++){
            if(i+p*minrep>n) break;
            string w=s.substr(i,p); long r=1;
            while(sw(s,w,i+r*p)) r++;
            if(r>=minrep && r*p>=mincover && (bestcov<0 || r*p>bestcov)){ bestcov=r*p; bp=p; br=r; }
        }
        if(bestcov>=0){
            int p=bp; long r=br; const Canon C=canon(s.substr(i,p)); string w=C.W; int o=C.r;
            if(o){ i+=o; r=1; while(sw(s,w,i+r*p)) r++; }
            if(r>=2){ if(loose<i) out.push_back({s.substr(loose,i-loose),1}); out.push_back({w,(i128)r}); i+=p*r; loose=i; }
            else i+=1;
        } else i+=1;
    }
    if(loose<n) out.push_back({s.substr(loose),1});
    return out;
}
static vector<Item> compress0(const string& s){
    vector<Item> items=compress1(s); int n=items.size();
    if(n<3) return items;
    vector<Item> out; int i=0;
    while(i<n){
        int hq=0, hr=0;
        for(int q=1;q<7;q++){
            if(i+3*q>n) break;
            int r=1;
            while(true){ int a=i+r*q; if(a+q>n) break; bool eq=true; for(int t=0;t<q;t++) if(!(items[a+t]==items[i+t])){eq=false;break;} if(!eq) break; r++; }
            if(r>=3 && (q>1 || items[i].c==1)){ hq=q; hr=r; break; }
        }
        if(hq){
            string X; for(int t=0;t<hq;t++){ for(i128 k=0;k<items[i+t].c;k++) X+=items[i+t].w; }
            const Canon C=canon(X);
            if(C.r==0) out.push_back({C.W,(i128)hr*C.k});
            else { string root=X.substr(0,C.W.size()); out.push_back({root.substr(0,C.r),1}); out.push_back({C.W,(i128)hr*C.k-1}); out.push_back({root.substr(C.r),1}); }
            i+=hq*hr;
        } else { out.push_back(items[i]); i++; }
    }
    return out;
}
static unordered_map<string,vector<Item>> cmemo; static size_t cmemo_bytes=0;
static vector<Item> compress(const string& s){
    auto it=cmemo.find(s); if(it!=cmemo.end()) return it->second;
    vector<Item> r=compress0(s); if(cmemo.size()>2000000 || cmemo_bytes>(size_t)400<<20){ cmemo.clear(); cmemo_bytes=0; } cmemo_bytes+=s.size()*2+64+r.size()*48; cmemo[s]=r; return r;
}
static string rep(const string& w, i128 c){ string s; s.reserve(w.size()*(size_t)c); for(i128 k=0;k<c;k++) s+=w; return s; }

// ---------------------------------------------------------------- buffer
struct Buf {
    vector<uint8_t> v; size_t st=0;
    size_t size() const { return v.size()-st; }
    uint8_t* p(){ return v.data()+st; }
    uint8_t& operator[](size_t i){ return v[st+i]; }
    void clear(){ v.clear(); st=0; }
    void prepend(const uint8_t* a, size_t n){
        if(st<n){ size_t sz=size(); size_t slack=max(n,sz)+256; vector<uint8_t> nv(slack+sz); memcpy(nv.data()+slack, v.data()+st, sz); v.swap(nv); st=slack; }
        st-=n; memcpy(v.data()+st, a, n);
    }
    void append(const uint8_t* a, size_t n){ v.insert(v.end(), a, a+n); }
    void erase_prefix(size_t n){ st+=n; if(st>65536 && st>2*size()){ v.erase(v.begin(), v.begin()+st); st=0; } }
    void erase_suffix_from(size_t i){ v.resize(st+i); }
    string str(size_t a, size_t b){ string s(b-a,'0'); for(size_t i=a;i<b;i++) s[i-a]='0'+v[st+i]; return s; }
};
static vector<uint8_t> cells(const string& w){ vector<uint8_t> a(w.size()); for(size_t i=0;i<w.size();i++) a[i]=w[i]-'0'; return a; }

struct Rule { char type; int D; string Tt; int P; string O; i128 st; int s1; string Orev; vector<uint8_t> Ob, Obr; void fin(){ Orev=string(O.rbegin(),O.rend()); Ob.resize(O.size()); for(size_t i=0;i<O.size();i++) Ob[i]=O[i]-'0'; Obr.assign(Ob.rbegin(),Ob.rend()); } };
static inline uint64_t hstep(uint64_t h, int c){ return (h ^ (uint64_t)(c+1)) * 0x100000001b3ULL + (h>>29); }
static uint64_t thash(const string& Tt){ uint64_t h=0xcbf29ce484222325ULL; for(long j=0;j<(long)Tt.size();j++) h=hstep(h, Tt[Tt.size()-1-j]-'0'); return h; }
struct Trans { int w, d, s; bool halt; };

struct Sample { uint64_t sig; vector<i128> counts; i128 steps; long lcm; };

struct RSim {
    int KEEP=1024, TRAIL=256, TRAILMAX=1024, K=10, MARGIN=8, BIG=8, TRAVEL=48; long SCRATCH_STEPS=400000;
    Trans T[8][2]; int nstates=0;
    Rope L,R; Buf buf; long h=0; i128 base=0; int s=0; i128 steps=0;
    unordered_map<string, deque<pair<int, unordered_map<uint64_t,Rule>>>> rules, prules;
    unordered_set<string> ptried, fail;
    bool jumps=true; string kbuf, tbuf; vector<uint64_t> hv;
    unordered_map<uint64_t, vector<long>> hist; vector<Sample> samples;
    int lastdir=1; i128 lastright=0, lastleft=0; long lcm=1;
    long nsampclear=0; unsigned long memtick=0; long memlimit=(long)5<<30; bool memout=false; bool timeout=false; double deadline=0, lastprog=0; chrono::steady_clock::time_point t0=chrono::steady_clock::now(); long njumps=0, nsamp=0, nrule=0, nlearn=0; i128 jumped=0; bool halted=false;
    vector<string> jlog; bool dojlog=false;

    RSim(const string& m, bool j=true): jumps(j) {
        int g=0; size_t i=0;
        while(i<m.size()){
            for(int r=0;r<2;r++){ string t=m.substr(i+3*r,3); if(t[0]=='-') T[g][r]={0,0,0,true}; else T[g][r]={t[0]-'0', t[1]=='R'?1:-1, t[2]-'A', false}; }
            g++; i+=7;
        }
        nstates=g; buf.v.assign(1,0); buf.st=0;
    }
    // ------------------------------------------------ ropes
    void _append(Rope& rope, const Item& it){ if(!rope.empty() && rope.back().w==it.w) rope.back().c+=it.c; else rope.push_back(it); }
    void _tidy(Rope& rope, bool left){
        while(true){
            int n=rope.size(); bool done=true; string t;
            long tl=0;
            for(int i=1;i<min(n,9);i++){
                Item& it=rope[n-i];
                if((i128)it.w.size()*it.c>4000) break;
                tl += (long)it.w.size()*(long)it.c;
                const string& W=rope[n-i-1].w;
                if((long)W.size()<=tl && W!=it.w){
                    // does the concatenation t of items n-i..n-1 (tape order) start (left) / end (right) with W?
                    bool m=true; size_t lwW=W.size();
                    if(left){ size_t pos=0; for(int k=n-i;k<n && pos<lwW && m;k++){ const string& x=rope[k].w; for(i128 r=0;r<rope[k].c && pos<lwW && m;r++) for(size_t a=0;a<x.size() && pos<lwW;a++){ if(x[a]!=W[pos]){m=false;break;} pos++; } } }
                    else { long pos=lwW-1; for(int k=n-i;k<n && pos>=0 && m;k++){ const string& x=rope[k].w; for(i128 r=0;r<rope[k].c && pos>=0 && m;r++) for(long a=x.size()-1;a>=0 && pos>=0;a--){ if(x[a]!=W[pos]){m=false;break;} pos--; } } }
                    if(m){
                        for(int k=1;k<=i;k++){ const Item& y=rope[n-k]; string piece=rep(y.w,y.c); t = left ? piece+t : t+piece; }
                        string rest = left ? t.substr(W.size()) : t.substr(0,t.size()-W.size());
                        rope.resize(n-i); rope.back().c+=1;
                        if(!rest.empty()){ vector<Item> cs=compress(rest); if(left) for(auto&x:cs) rope.push_back(x); else for(int k=cs.size()-1;k>=0;k--) rope.push_back(cs[k]); }
                        done=false; break;
                    }
                }
            }
            if(!done) continue;
            for(int q=1;q<7;q++){
                if(n>=3*q){
                    bool eq=true;
                    for(int t2=0;t2<q && eq;t2++){ const Item&a=rope[n-q+t2]; const Item&b=rope[n-2*q+t2]; const Item&c=rope[n-3*q+t2]; if(!(a==b && b==c)) eq=false; }
                    if(eq){
                        string X; long tot=0; bool big=false;
                        for(int t2=0;t2<q;t2++){ const Item& a = left? rope[n-q+t2] : rope[n-1-t2]; i128 len=(i128)a.w.size()*a.c; tot+= (len>100000? 100000:(long)len); if(tot>4000){big=true;break;} X+=rep(a.w,a.c); }
                        if(big || X.size()>4000) continue;
                        rope.resize(n-3*q); _pushrun(rope,left,X,3); done=false; break;
                    }
                }
            }
            if(done) return;
        }
    }
    void _pushstr(Rope& rope, bool left, string s){
        if(rope.empty()){
            if(left){ size_t a=s.find_first_not_of('0'); s = a==string::npos? "" : s.substr(a); }
            else { size_t b=s.find_last_not_of('0'); s = b==string::npos? "" : s.substr(0,b+1); }
        }
        if(s.empty()) return;
        vector<Item> items=compress(s);
        if(left) for(auto&x:items) _append(rope,x); else for(int k=items.size()-1;k>=0;k--) _append(rope,items[k]);
        _tidy(rope,left);
    }
    void _pushrun(Rope& rope, bool left, const string& O, i128 J){
        if(J<=0) return;
        const Canon C=canon(O); int p=C.W.size();
        if(C.r==0){ _append(rope,{C.W,J*C.k}); _tidy(rope,left); return; }
        string root=O.substr(0,p), pre=root.substr(0,C.r), post=root.substr(C.r);
        if(left){ _pushstr(rope,left,pre); if(J*C.k>1) _append(rope,{C.W,J*C.k-1}); _pushstr(rope,left,post); }
        else { _pushstr(rope,left,post); if(J*C.k>1) _append(rope,{C.W,J*C.k-1}); _pushstr(rope,left,pre); }
    }
    void pushR(const string& s){ _pushstr(R,false,s); }
    void pushL(const string& s){ _pushstr(L,true,s); }
    void flush(){
        if(h>2*KEEP){ long cut=h-KEEP; pushL(buf.str(0,cut)); buf.erase_prefix(cut); h-=cut; base+=cut; }
        if((long)buf.size()-h>2*KEEP){ long cut=h+KEEP; pushR(buf.str(cut,buf.size())); buf.erase_suffix_from(cut); }
    }
    void flush_all(){
        if(h>0) pushL(buf.str(0,h));
        if(h<(long)buf.size()) pushR(buf.str(max(h,0L),buf.size()));
        base+=h; buf.clear(); h=0;
    }
    void ensure_behind(int d, long D){
        while((long)buf.size()<D){
            Rope& rope = d<0? R : L;
            vector<uint8_t> add;
            if(rope.empty()) add.assign(64,0);
            else { Item& it=rope.back(); add=cells(it.w); it.c-=1; if(it.c==0) rope.pop_back(); }
            if(d<0) buf.append(add.data(),add.size());
            else { buf.prepend(add.data(),add.size()); h+=add.size(); base-=add.size(); }
        }
    }
    // ------------------------------------------------ learning
    struct Rec { int s; long steps; long D; };
    void scratch(int s, int d, const vector<uint8_t>& wf, const vector<uint8_t>& tr, int Kc, vector<Rec>& recs, vector<vector<uint8_t>>& snaps){
        long lt=tr.size(), lw=wf.size();
        vector<uint8_t> arr(tr); for(int k=0;k<Kc;k++) arr.insert(arr.end(),wf.begin(),wf.end());
        long pos=lt, nextb=lt+lw, lo=pos; long st=0;
        snaps.push_back(arr);
        while(st<SCRATCH_STEPS){
            if(pos>=nextb){
                recs.push_back({s,st,max(nextb-lw-lo,0L)}); snaps.push_back(arr);
                if((int)recs.size()==Kc) break;
                lo=pos; nextb+=lw;
            }
            if(pos<0) break;
            const Trans& t=T[s][arr[pos]];
            if(t.halt) break;
            arr[pos]=t.w; pos+=t.d*d; s=t.s; st++;
            if(pos<lo) lo=pos;
        }
    }
    static string key3(int s,int d,const string& w){ string k; k+=char('A'+s); k+= d<0?'-':'+'; k+=w; return k; }
    static string v2s(const uint8_t* a, size_t n){ string s(n,'0'); for(size_t i=0;i<n;i++) s[i]='0'+a[i]; return s; }
    const Rule* addrule(int st, int d, const string& w, int D, const string& Tt, Rule r){
        r.fin();
        auto& tabs = r.type=='P'? prules : rules;
        auto& byD = tabs[key3(st,d,w)];
        uint64_t hk=thash(Tt);
        for(auto& pr: byD) if(pr.first==D){ auto f=pr.second.find(hk); if(f!=pr.second.end() && f->second.Tt!=Tt){ fprintf(stderr,"hash collision\n"); exit(3);} pr.second[hk]=r; return &pr.second[hk]; }
        byD.push_back({D,{}}); byD.back().second[hk]=r; return &byD.back().second[hk];
    }
    bool learn(int d, bool force, const Rule*& out){
        Rope& rope = d<0? L : R;
        string w=rope.back().w; i128 c=rope.back().c;
        int s0=s;
        ensure_behind(d,TRAIL);
        vector<uint8_t> tr, wf;
        size_t n=buf.size();
        if(d<0){ size_t m=min((size_t)TRAILMAX,n); tr.assign(buf.p(),buf.p()+m); reverse(tr.begin(),tr.end()); wf=cells(w); reverse(wf.begin(),wf.end()); }
        else { size_t m=min((size_t)TRAILMAX,n); tr.assign(buf.p()+n-m,buf.p()+n); wf=cells(w); }
        size_t tk=min((size_t)128,tr.size());
        string key=key3(s0,d,w)+"|"+v2s(tr.data()+tr.size()-tk,tk);
        if(fail.size()>3000000) fail.clear();
        if(fail.count(key) && !force) return false;
        nlearn++;
        int Kc = c<K? (int)c : K;
        vector<Rec> recs; vector<vector<uint8_t>> snaps;
        scratch(s0,d,wf,tr,Kc,recs,snaps);
        long lt=tr.size(), lw=wf.size();
        if(recs.empty()){ fail.insert(key); return false; }
        bool have=false;
        if(recs.size()>=2){
            vector<int> states{s0}; vector<long> stp{0}; vector<long> Ds;
            for(auto&r:recs){ states.push_back(r.s); stp.push_back(r.steps); Ds.push_back(r.D); }
            int fi=-1,fj=-1; long fD=0; int nr=recs.size();
            for(int i=0;i<nr && fi<0;i++) for(int j=i+1;j<=nr;j++){
                if(states[i]!=states[j]) continue;
                long D=0; for(int k=i;k<j;k++) D=max(D,Ds[k]);
                long bi=lt+i*lw, bj=lt+j*lw;
                if(D>bi) continue;
                if(equal(snaps[i].begin()+bi-D, snaps[i].begin()+bi, snaps[j].begin()+bj-D)){ fi=i; fj=j; fD=D; break; }
            }
            if(fi>=0){
                long bi=lt+fi*lw, bj=lt+fj*lw;
                Rule pr; pr.type='P'; pr.D=fD; pr.Tt=v2s(snaps[fi].data()+bi-fD,fD); pr.P=fj-fi; pr.O=v2s(snaps[fj].data()+bi-fD, bj-bi); pr.st=stp[fj]-stp[fi]; pr.s1=states[fi];
                const Rule* q=addrule(states[fi],d,w,fD,pr.Tt,pr);
                if(fi==0){ out=q; have=true; }
            }
        }
        if(!have){
            Rule tr2; tr2.type='T'; tr2.s1=recs[0].s; tr2.D=recs[0].D; tr2.st=recs[0].steps; tr2.P=1;
            tr2.Tt=v2s(tr.data()+lt-tr2.D, tr2.D); tr2.O=v2s(snaps[1].data()+lt-tr2.D, tr2.D+lw);
            out=addrule(s0,d,w,tr2.D,tr2.Tt,tr2); have=true;
        }
        return have;
    }
    const Rule* lookup(unordered_map<string, deque<pair<int, unordered_map<uint64_t,Rule>>>>& tabs, int d, const string& w, i128 c){
        kbuf.clear(); kbuf+=char('A'+s); kbuf+= d<0?'-':'+'; kbuf+=w;
        auto it=tabs.find(kbuf); if(it==tabs.end()) return nullptr;
        hv.clear(); hv.push_back(0xcbf29ce484222325ULL);
        for(auto& pr: it->second){
            int D=pr.first;
            if((long)buf.size()<D) ensure_behind(d,D);
            while((int)hv.size()<=D){ size_t j=hv.size()-1; int cc = d<0? buf[j] : buf[buf.size()-1-j]; hv.push_back(hstep(hv.back(),cc)); }
            auto r=pr.second.find(hv[D]);
            if(r!=pr.second.end()){
                const string& Tt=r->second.Tt; bool eq=true;
                for(int k=0;k<D;k++){ int cc = d<0? buf[D-1-k] : buf[buf.size()-D+k]; if(Tt[k]-'0'!=cc){eq=false;break;} }
                if(!eq){ fprintf(stderr,"hash collision in lookup\n"); exit(3); }
                if(r->second.type=='T' || c>=r->second.P) return &r->second;
            }
        }
        return nullptr;
    }
    bool find(int d, const Rule*& out){
        Rope& rope = d<0? L : R;
        const string& w=rope.back().w; i128 c=rope.back().c;
        if(c>=2){ const Rule* r=lookup(prules,d,w,c); if(r){ out=r; return true; } }
        const Rule* r=lookup(rules,d,w,c);
        if(r && c>=2){
            string key=key3(s,d,w)+"|"+to_string(r->D)+"|"+r->Tt;
            if(ptried.size()>3000000) ptried.clear();
            if(!ptried.count(key)){
                ptried.insert(key);
                string wc=w; const Rule* r2=nullptr;
                if(learn(d,true,r2) && r2->type=='P' && c>=r2->P){ out=r2; return true; }
            }
            out=r; return true;
        }
        if(r){ out=r; return true; }
        return false;
    }
    void apply(int d, const Rule& rule){
        Rope& rope = d<0? L : R;
        size_t lw=rope.back().w.size(); i128 c=rope.back().c;
        int D=rule.D; nrule++;
        if(rule.type=='P'){
            if(d<0){ if((long)buf.size()>D){ pushR(buf.str(D,buf.size())); buf.erase_suffix_from(D); } }
            else { if((long)buf.size()>D){ long cut=buf.size()-D; pushL(buf.str(0,cut)); buf.erase_prefix(cut); base+=cut; } }
            i128 J=c/rule.P;
            if(d<0){ _pushrun(R,false,rule.Orev,J); base-=J*rule.P*(i128)lw; h=-1; }
            else { _pushrun(L,true,rule.O,J); base+=J*rule.P*(i128)lw; h=buf.size(); }
            steps+=J*rule.st;
            rope.back().c-=J*rule.P; if(rope.back().c==0) rope.pop_back();
            if(rule.P>1) lcm = lcm*rule.P/std::gcd(lcm,(long)rule.P);
        } else {
            if(d<0){ buf.erase_prefix(D); buf.prepend(rule.Obr.data(),rule.Obr.size()); base-=lw; h=-1; }
            else { if(D) buf.erase_suffix_from(buf.size()-D); buf.append(rule.Ob.data(),rule.Ob.size()); h=buf.size(); }
            s=rule.s1; steps+=rule.st;
            rope.back().c-=1; if(rope.back().c==0) rope.pop_back();
        }
    }
    void edge(int d){
        if(d!=lastdir){
            if(d>0){ if(jumps && lastright-lastleft>=TRAVEL) sample(); }
            lastdir=d;
        }
        if(d>0) lastright=base+h; else lastleft=base+h;
        Rope& rope = d<0? L : R;
        if(rope.empty()){
            vector<uint8_t> z(64,0);
            if(d<0){ buf.prepend(z.data(),64); h+=64; base-=64; } else buf.append(z.data(),64);
            return;
        }
        const Rule* rule=nullptr; bool ok=find(d,rule);
        if(!ok){
            ok=learn(d,false,rule);
            if(ok && rule->type=='P' && rope.back().c<rule->P) ok=false;
        }
        if(ok){ apply(d,*rule); return; }
        Item& it=rope.back(); vector<uint8_t> add=cells(it.w); it.c-=1; if(it.c==0) rope.pop_back();
        if(d<0){ buf.prepend(add.data(),add.size()); h+=add.size(); base-=add.size(); }
        else buf.append(add.data(),add.size());
    }
    // ------------------------------------------------ samples and jumps
    uint64_t signature(vector<Item*>& refs, vector<i128>& counts){
        flush_all();
        string sig; vector<char> dummy;
        size_t a=0; while(a<L.size() && L[a].w.find('1')==string::npos) a++;
        long b=R.size(); // Rs = R reversed; strip from the far right end = R[0..]
        long rb=0; while(rb<(long)R.size() && R[rb].w.find('1')==string::npos) rb++;   // R[0] is the far right
        string loose;
        auto flushloose=[&](){ if(!loose.empty()){ sig+="S"; sig+=loose; sig+=";"; loose.clear(); } };
        for(size_t k=a;k<L.size();k++){ Item& it=L[k]; if(it.c>=BIG){ flushloose(); sig+="W"; sig+=it.w; sig+=";"; refs.push_back(&it); counts.push_back(it.c);} else loose+=rep(it.w,it.c); }
        flushloose(); sig+="H"; sig+=char('A'+s); sig+=";";
        for(long k=b-1;k>=rb;k--){ Item& it=R[k]; if(it.c>=BIG){ flushloose(); sig+="W"; sig+=it.w; sig+=";"; refs.push_back(&it); counts.push_back(it.c);} else loose+=rep(it.w,it.c); }
        flushloose();
        return hash<string>()(sig) ^ (sig.size()*0x9E3779B97F4A7C15ULL);
    }
    void sample(){
        vector<Item*> refs; vector<i128> counts;
        uint64_t sig=signature(refs,counts);
        if(samples.size()>1000000){ samples.clear(); hist.clear(); nsampclear++; }
        long idx=samples.size(); nsamp++;
        samples.push_back({sig,counts,steps,lcm}); lcm=1;
        auto& prev=hist[sig]; prev.push_back(idx);
        int tried=0;
        long np=prev.size();
        for(long q=np-2; q>=0 && q>np-200; q--){
            long i=prev[q]; long P=idx-i;
            if(idx-2*P<0) break;
            if(samples[idx-2*P].sig!=sig) continue;
            tried++; if(tried>12) break;
            if(tryjump(idx,P,sig,refs,counts)) return;
        }
    }
    bool tryjump(long idx, long P, uint64_t sig, vector<Item*>& refs, vector<i128>& counts){
        auto& S=samples;
        if(idx-2*P<0 || S[idx-2*P].sig!=sig || S[idx-P].counts.size()!=counts.size()) return false;
        size_t nc=counts.size(); vector<i128> d(nc); bool any=false;
        for(size_t k=0;k<nc;k++){ d[k]=counts[k]-S[idx-P].counts[k]; if(d[k]) any=true; }
        if(!any) return false;
        long n=2, lc=1;
        while(true){
            if(idx-n*P<0) return false;
            lc=1;
            for(long t=0;t<n*P;t++){ long l=S[idx-t].lcm; lc=lc*l/std::gcd(lc,l); }
            if(lc+1<=n) break;
            n=lc+1;
        }
        for(long t=1;t<=n;t++){
            long i0=idx-t*P;
            if(S[i0].sig!=sig || S[i0].counts.size()!=nc) return false;
            for(size_t k=0;k<nc;k++) if(S[i0+P].counts[k]-S[i0].counts[k]!=d[k]) return false;
        }
        for(long t=0;t<P;t++) for(long u=1;u<n;u++) if(S[idx-t].sig!=S[idx-t-u*P].sig) return false;
        vector<i128> e(n), f(n-1);
        for(long t=0;t<n;t++) e[t]=S[idx-t*P].steps-S[idx-(t+1)*P].steps;
        for(long t=0;t<n-1;t++) f[t]=e[t]-e[t+1];
        for(auto x: f) if(x!=f[0]) return false;
        bool hasJ=false; i128 J=0;
        for(size_t k=0;k<nc;k++) if(d[k]<0){ i128 j=floordiv(counts[k]-MARGIN-2*lc, -d[k]); if(!hasJ || j<J){ J=j; hasJ=true; } }
        if(hasJ && J>=2){
            for(size_t k=0;k<nc;k++) refs[k]->c+=J*d[k];
            steps+=J*e[0]+f[0]*J*(J+1)/2;
            njumps++; jumped+=J*P;
            if(dojlog) jlog.push_back(i2s(steps)+" J="+i2s(J)+" P="+to_string(P));
            hist.clear(); samples.clear();
            return true;
        }
        return false;
    }
    // ------------------------------------------------ run
    bool run(i128 maxsteps){
        while(steps<maxsteps){
            long n=buf.size(); i128 lim=maxsteps-steps; if(lim>200000) lim=200000;
            long k=0, L2=(long)lim; uint8_t* B=buf.p(); long hh=h; int ss=s;
            while(hh>=0 && hh<n && k<L2){
                const Trans& t=T[ss][B[hh]];
                if(t.halt){ h=hh; s=ss; steps+=k+1; halted=true; return false; }
                B[hh]=t.w; hh+=t.d; ss=t.s; k++;
            }
            h=hh; s=ss; steps+=k;
            if(h<0) edge(-1); else if(h>=n) edge(1);
            if((long)buf.size()>4*KEEP) flush();
            if(((++memtick)&0xFFFFF)==0){ long pages=0,rss=0; FILE* f=fopen("/proc/self/statm","r"); if(f){ if(fscanf(f,"%ld %ld",&pages,&rss)!=2) rss=0; fclose(f);} if(rss*4096L > memlimit){ memout=true; return true; }
                if(deadline>0){ double e=chrono::duration<double>(chrono::steady_clock::now()-t0).count(); if(e>deadline){ timeout=true; return true; } if(e-lastprog>=300){ lastprog=e; printf("%9.1fs steps %s (10^%.2f) items %zu jumps %ld rules %ld\n", e, i2s(steps).c_str(), log10((double)steps), L.size()+R.size(), njumps, nrule); fflush(stdout); } } }
            if(timeout) return true;
            if(memout) return true;
        }
        return true;
    }
    size_t nitems(){ return L.size()+R.size(); }
    // whole tape: string between, head offset into it
    void tape(string& out, long& hp){
        string left; for(auto& it:L) left+=rep(it.w,it.c);
        string mid=buf.str(0,buf.size());
        string right; for(long k=R.size()-1;k>=0;k--) right+=rep(R[k].w,R[k].c);
        out=left+mid+right; hp=left.size()+h;
    }
};

int main(int argc, char** argv){
    if(argc<3){ fprintf(stderr,"usage: rsim MACHINE MODE ...\n  at T1,T2,..   print 'steps state hp tape' after run(Ti) (jumps on unless NOJUMP env)\n  run SECONDS [JSON]  run with growing targets, progress to stdout\n"); return 2; }
    string m=argv[1], mode=argv[2];
    RSim sim(m, getenv("NOJUMP")==nullptr);
    sim.KEEP = getenv("KEEP")? atoi(getenv("KEEP")) : 32;
    if(getenv("MEMGB")) sim.memlimit=(long)(atof(getenv("MEMGB"))*(1L<<30));
    if(mode=="at"){
        string ts=argv[3]; stringstream ss(ts); string tok;
        while(getline(ss,tok,',')){
            i128 t=(i128)strtold(tok.c_str(),nullptr);
            bool ok=sim.run(t);
            string tp; long hp; sim.tape(tp,hp);
            printf("%s %c %ld %s %s nrule=%ld nlearn=%ld jumps=%ld nsamp=%ld items=%zu\n", i2s(sim.steps).c_str(), 'A'+sim.s, hp, ok?"run":"HALT", tp.c_str(), sim.nrule, sim.nlearn, sim.njumps, sim.nsamp, sim.nitems());
            fflush(stdout);
            if(!ok) break;
        }
        return 0;
    }
    if(mode=="items"){
        string ts=argv[3]; stringstream ss(ts); string tok;
        while(getline(ss,tok,',')){
            bool ok=sim.run((i128)strtold(tok.c_str(),nullptr));   // printed without changing the simulator's state
            printf("%s %c %s |", i2s(sim.steps).c_str(), 'A'+sim.s, ok?"run":"HALT");
            for(auto& it: sim.L){ if(it.c==1) printf(" %s",it.w.c_str()); else printf(" (%s)^%s",it.w.c_str(),i2s(it.c).c_str()); }
            { string b=sim.buf.str(0,sim.buf.size()); long h=sim.h; if(h<0) printf(" [HEAD at %ld]",h); printf(" "); for(long k=0;k<(long)b.size();k++){ if(k==h) printf("[%c>]",'A'+sim.s); putchar(b[k]); } if(h>=(long)b.size()) printf("[%c>]",'A'+sim.s); }
            for(long k=sim.R.size()-1;k>=0;k--){ auto& it=sim.R[k]; if(it.c==1) printf(" %s",it.w.c_str()); else printf(" (%s)^%s",it.w.c_str(),i2s(it.c).c_str()); }
            printf("\n"); fflush(stdout);
        }
        return 0;
    }
    if(mode=="stats"){
        string ts=argv[3]; stringstream ss(ts); string tok;
        while(getline(ss,tok,',')){
            i128 t=(i128)strtold(tok.c_str(),nullptr);
            bool ok=sim.run(t);
            printf("%s %c nrule=%ld nlearn=%ld jumps=%ld nsamp=%ld items=%zu %s\n", i2s(sim.steps).c_str(), 'A'+sim.s, sim.nrule, sim.nlearn, sim.njumps, sim.nsamp, sim.nitems(), ok?"":"HALT");
            fflush(stdout); if(!ok) break;
        }
        return 0;
    }
    if(mode=="run"){
        double secs=atof(argv[3]); auto t0=chrono::steady_clock::now(); sim.t0=t0; sim.deadline=secs;
        auto el=[&](){ return chrono::duration<double>(chrono::steady_clock::now()-t0).count(); };
        i128 target=1000000; bool ok=true; double lastp=-1;
        bool dec = getenv("DECADES")!=nullptr;  // targets of rsim_screen.py: 1e6..1e10 (with 3e9), then x10
        vector<i128> sched={1000000,10000000,100000000,1000000000,3000000000LL,10000000000LL}; size_t si=0;
        if(dec) target=sched[0];
        while(el()<secs){
            ok=sim.run(target); if(!ok || sim.memout || sim.timeout) break;
            if(dec){ si++; target = si<sched.size()? sched[si] : (si==sched.size()? (i128)100000000000LL : target*10); }
            else target = target + target/2 + 1;
            if(target > (i128)1e36L) target=(i128)1e36L;
            if(dec || el()-lastp>30){ lastp=el(); printf("%9.1fs steps %s (10^%.2f) items %zu jumps %ld rules %ld\n", el(), i2s(sim.steps).c_str(), log10(i2d(sim.steps)), sim.nitems(), sim.njumps, sim.nrule); fflush(stdout); }
        }
        if(sim.memout) printf("MEMORY limit reached\n");
        printf("FINAL %s steps %s (10^%.3f) sec %.1f jumps %ld samples %ld skipped %s items %zu rules %ld\n", ok?"running":"HALT", i2s(sim.steps).c_str(), log10(i2d(sim.steps)), el(), sim.njumps, sim.nsamp, i2s(sim.jumped).c_str(), sim.nitems(), sim.nrule);
        if(argc>4){ FILE* f=fopen(argv[4],"w"); fprintf(f,"{\"machine\": \"%s\", \"halt\": %s, \"reached\": %s, \"sec\": %.1f, \"jumps\": %ld, \"samples\": %ld, \"skipped\": %s, \"items\": %zu}\n", m.c_str(), ok?"null":i2s(sim.steps).c_str(), i2s(sim.steps).c_str(), el(), sim.njumps, sim.nsamp, i2s(sim.jumped).c_str(), sim.nitems()); fclose(f); }
        return 0;
    }
    return 2;
}
