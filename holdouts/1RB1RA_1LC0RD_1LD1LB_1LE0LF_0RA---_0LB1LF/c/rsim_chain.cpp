// rsim.cpp: C++ port of holdouts/.../py/rsim.py (same algorithm, same constants, same order of decisions).
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
            if(turnhist && d>0 && steps>=visit_from){ size_t k=L.size(); if(k>=th.size()) th.resize(k+1,0); th[k]++; }
            if(d>0 && stop_at_visit && lastright-lastleft>=TRAVEL){ flush_all(); if(L.size()<=LMAXV && is_incr()){ stopped=true; lastdir=d; lastright=base+h; return; } }
            if(d>0){ if(jumps && lastright-lastleft>=TRAVEL) sample(); else if(!jumps && visit_n>0 && visit_from>=0 && steps>=visit_from && lastright-lastleft>=TRAVEL){ flush_all(); if(L.size()<=2){ visit_n--; printvisit(); } } }
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
    bool stop_at_visit=false, stopped=false; long rulestop=0; size_t LMAXV = getenv("LMAXV")? atol(getenv("LMAXV")) : 1000;
    bool is_incr(){   // right rope starts with 1^odd 00 10
        if(R.empty()) return false; const Item& a=R.back(); if(a.w!="1" || a.c%2==0 || a.c<81) return false;
        string t; for(long k=(long)R.size()-2;k>=0 && t.size()<8;k--){ t+=rep(R[k].w, R[k].c>8? 8:R[k].c); }
        return t.compare(0,4,"0010")==0;
    }
    long double visit_from=-1; long visit_n=0; long visit_maxL=2; long visit_maxitems=1000000; bool turnhist=false; vector<long> th;
    void printitem(const Item& it){ if(it.c==1) printf(" %s",it.w.c_str()); else printf(" (%s)^%s",it.w.c_str(),i2s(it.c).c_str()); }
    void printvisit(){ printf("V %s %c |",i2s(steps).c_str(),'A'+s); for(auto&it:L) printitem(it); printf(" ||"); for(long k=R.size()-1;k>=0;k--) printitem(R[k]); printf("\n"); }
    void sample(){
        vector<Item*> refs; vector<i128> counts;
        uint64_t sig=signature(refs,counts);
        if(visit_from>=0 && steps>=visit_from && visit_n>0 && L.size()<=(size_t)visit_maxL && L.size()+R.size()<=(size_t)visit_maxitems){ visit_n--; printvisit(); }
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
            if(stopped){ stopped=false; return true; }
            if(rulestop && nrule>=rulestop) return true;
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


// ======================================================================== chain-phase engine
// At an increment visit the right rope is  D(a0) s0 D(a1) s1 ... D(aL) tail | boundary item (count >= 50, word != "1") ...
// D(a) = 1^(2a+1) 00; levels are the D's with a >= AMIN; s_k and tail are short cell strings.
static const long AMIN=12;
struct TapeSnap { Rope L,R; Buf buf; long h; i128 base; int s; i128 steps; int lastdir; i128 lastright,lastleft; long lcm; };
static TapeSnap snapof(RSim& m){ return {m.L,m.R,m.buf,m.h,m.base,m.s,m.steps,m.lastdir,m.lastright,m.lastleft,m.lcm}; }
static void restoreto(RSim& m,const TapeSnap& t){ m.L=t.L; m.R=t.R; m.buf=t.buf; m.h=t.h; m.base=t.base; m.s=t.s; m.steps=t.steps; m.lastdir=t.lastdir; m.lastright=t.lastright; m.lastleft=t.lastleft; m.lcm=t.lcm; }

static unordered_map<string,int> sepid; static vector<string> sepstr;
static int sid(const string& x){ auto it=sepid.find(x); if(it!=sepid.end()) return it->second; int k=sepstr.size(); sepstr.push_back(x); sepid[x]=k; return k; }

struct Extra { int side; size_t idx; i128 c; };   // a big count outside the chain region: side 0 = L[idx], 1 = R[idx]
struct MState { string rest; int restid=-1;
    vector<i128> a; vector<int> sep; string tail;
    size_t bidx;                 // R[bidx] is the boundary item; R[0..bidx] stay as they are
    vector<Extra> ex;
    int state;                   // machine state at the visit
};
// parse the simulator's tape at an increment visit
static bool parse(RSim& m, MState& P){
    if(m.buf.size()!=0) return false;
    P.a.clear(); P.sep.clear(); P.tail.clear(); P.ex.clear(); P.state=m.s;
    long k=(long)m.R.size()-1; vector<pair<char,i128>> runs;
    auto add=[&](char ch,i128 n){ if(!runs.empty() && runs.back().first==ch) runs.back().second+=n; else runs.push_back({ch,n}); };
    long small=0;
    for(;k>=0;k--){
        const Item& it=m.R[k];
        if(it.w.find('0')==string::npos){ add('1',it.c*(i128)it.w.size()); continue; }
        if(it.c>=50) break;
        if((i128)it.w.size()*it.c>4000) return false;
        for(i128 r=0;r<it.c;r++) for(char ch:it.w) add(ch,1);
    }
    if(k<0) return false;
    P.bidx=k;
    // tokens
    size_t i=0; string cur; bool started=false;
    while(i<runs.size()){
        auto& r=runs[i];
        if(r.first=='1' && r.second%2==1 && r.second>=2*AMIN+1 && i+1<runs.size() && runs[i+1].first=='0' && runs[i+1].second==2){
            if(started) P.sep.push_back(sid(cur)); else if(!cur.empty()) return false;
            P.a.push_back((r.second-1)/2); started=true; cur.clear(); i+=2; continue;
        }
        if(!started) return false;
        if(r.second>200) return false;
        cur+=string((size_t)r.second, r.first); small+= (long)r.second; if(small>20000) return false;
        i++;
    }
    P.tail=cur;
    if(P.a.size()<6) return false;
    P.rest.clear();
    for(size_t j=0;j<m.L.size();j++){ if(m.L[j].c>=50){ P.ex.push_back({0,j,m.L[j].c}); P.rest+="|"+m.L[j].w+"^*|"; } else { if((i128)m.L[j].w.size()*m.L[j].c>20000) return false; P.rest+=rep(m.L[j].w,m.L[j].c); } }
    P.rest+="#";
    for(long j=(long)P.bidx;j>=0;j--){ if(m.R[j].c>=50){ P.ex.push_back({1,(size_t)j,m.R[j].c}); P.rest+="|"+m.R[j].w+"^*|"; } else { if((i128)m.R[j].w.size()*m.R[j].c>20000) return false; P.rest+=rep(m.R[j].w,m.R[j].c); } }
    P.restid=sid(P.rest);
    return true;
}
// write a chain state back into the simulator (the left rope and R[0..bidx] are reused with updated counts)
static vector<long> levitem;   // R index of each level's ones item after materialize
static void materialize(RSim& m, const MState& P){
    for(auto& e:P.ex){ if(e.side==0) m.L[e.idx].c=e.c; else m.R[e.idx].c=e.c; }
    m.R.resize(P.bidx+1);
    vector<Item> its;  // tape order
    levitem.assign(P.a.size(),-1);
    vector<int> lvpos;
    for(size_t k=0;k<P.a.size();k++){
        lvpos.push_back(its.size()); its.push_back({"1",2*P.a[k]+1});
        string lit="00"+(k+1<P.a.size()? sepstr[P.sep[k]] : P.tail);
        for(auto& x: compress(lit)) its.push_back(x);
    }
    for(long j=(long)its.size()-1;j>=0;j--) m.R.push_back(its[j]);
    for(size_t k=0;k<P.a.size();k++) levitem[k]=(long)m.R.size()-1-lvpos[k];
    m.buf.clear(); m.h=0; m.s=P.state;
}
// one exact increment by the simulator; returns false if it did not reach the next visit within the budget
static long ofail[4];
static bool oracle(RSim& m, long budget){
    bool j=m.jumps; m.jumps=false; m.stop_at_visit=true; m.rulestop=m.nrule+budget;
    long rs=m.rulestop; bool ok=m.run((i128)1e36L); m.rulestop=0; m.jumps=j;
    if(!ok || m.halted || m.timeout || m.memout){ ofail[0]++; return false; }
    if(m.nrule>=rs){ ofail[1]++; return false; }
    if(m.buf.size()!=0 || !m.is_incr()){ ofail[2]++; return false; }
    return true;
}
struct CAkey { int cls,l,c,r,q=0; bool operator==(const CAkey&o) const { return cls==o.cls&&l==o.l&&c==o.c&&r==o.r&&q==o.q; } };
struct CAkh { size_t operator()(const CAkey&k) const { return ((size_t)k.q*7777777u ^ (size_t)k.cls*1000003u ^ (size_t)(k.l+7)*10007u ^ (size_t)(k.c+7)*101u ^ (size_t)(k.r+7)); } };
struct CAval { int nw; int dv; };
static unordered_map<CAkey,CAval,CAkh> ca;   // sep k: (class, sep[k-1], sep[k], sep[k+1]) -> (new sep[k], change of a[k+1]); class -1 = a0's change
struct CostModel { i128 c0; vector<i128> wl, wp; vector<i128> we; long uses=0; vector<int> lsep; vector<i128> la, lex; string ltail; };
static unordered_map<string,CostModel> costs;
static map<string,vector<i128>> exd;
static string exshape(const MState& P){ return "R"+to_string(P.restid); }
static unordered_set<long long> cabad; static long long cak(const CAkey&k){ return ((((long long)(k.cls+2)*100003+(k.l+7))*100003+(k.c+7))*100003+(k.r+7))*3310007LL+k.q; }
static long ca_conflicts=0;
static int cls(size_t k){ return k==0?0:(k==1?1:2); }
static int qrel(const MState& P, size_t k){ if(k+1>=P.a.size()) return 2; i128 d=2*P.a[k+1]-P.a[k]; return (d>=-4 && d<=4)? 0 : 1; }
static int qsig(const MState& P, size_t k){ int x=0; for(long j=(long)k-1;j<=(long)k+2;j++){ x*=3; if(j>=0) x+=qrel(P,j); } return x; }
static CAkey keyfor(const MState& P, const MState& Q, size_t k){ int l = k==0? -1 : P.sep[k-1]; int r = k+1<P.sep.size()? P.sep[k+1] : -2; CAkey K{cls(k),l,P.sep[k],r}; K.q=qsig(P,k)*1000 + (k==0? (int)(Q.a[0]-P.a[0])+500 : Q.sep[k-1]); return K; }
static CAkey key0(const MState& P){ CAkey K{-1,P.sep.size()>2?P.sep[2]:-2,P.sep[0],P.sep.size()>1?P.sep[1]:-2}; K.q=qsig(P,0)*1000+(P.sep.size()>3?P.sep[3]:999)+ (int)(P.a[0]&1)*7000000; return K; }
static bool same_shape(const MState& A, const MState& B){
    if(A.restid!=B.restid || A.a.size()!=B.a.size() || A.ex.size()!=B.ex.size() || A.tail!=B.tail || A.state!=B.state) return false;
    return true;
}
// learn the automaton from an observed increment P -> Q
static bool learn_ca(const MState& P, const MState& Q){
    if(!same_shape(P,Q)) return false;
    vector<pair<CAkey,CAval>> obs;
    obs.push_back({key0(P),{-1,(int)(Q.a[0]-P.a[0])}});
    for(size_t k=0;k<P.sep.size();k++) obs.push_back({keyfor(P,Q,k),{Q.sep[k],(int)(Q.a[k+1]-P.a[k+1])}});
    bool bad=false;
    for(auto& o:obs){ auto it=ca.find(o.first); if(it==ca.end()) ca[o.first]=o.second; else if(it->second.nw!=o.second.nw || it->second.dv!=o.second.dv){ ca_conflicts++; cabad.insert(cak(o.first)); bad=true; if(getenv("SHOWCONF")){ fprintf(stderr,"CONF cls %d l %d c %d r %d : was %d/%d now %d/%d | a:",o.first.cls,o.first.l,o.first.c,o.first.r,it->second.nw,it->second.dv,o.second.nw,o.second.dv); for(auto x:P.a) fprintf(stderr," %s",i2s(x).c_str()); fprintf(stderr," seps:"); for(auto x:P.sep) fprintf(stderr," %d",x); fprintf(stderr,"\n"); } } }
    if(bad) return false;
    vector<i128> d; for(size_t i=0;i<P.ex.size();i++) d.push_back(Q.ex[i].c-P.ex[i].c);
    string sh=exshape(P); auto e=exd.find(sh);
    if(e==exd.end()) exd[sh]=d; else if(e->second!=d){ return false; }
    return true;
}
static string costkey(const MState& P, const MState& Q){
    string k=to_string(P.a.size())+"|"+to_string((long)(Q.a[0]-P.a[0]));
    for(size_t j=0;j<P.sep.size();j++) if(P.sep[j]!=Q.sep[j] || Q.a[j+1]!=P.a[j+1]) k+="|"+to_string(j)+":"+to_string(P.sep[j])+">"+to_string(Q.sep[j])+":"+to_string((long)(Q.a[j+1]-P.a[j+1]));
    { static long W = getenv("KW")? atol(getenv("KW")) : 2; long mx=-1; for(size_t jj=0;jj<P.sep.size();jj++) if(P.sep[jj]!=Q.sep[jj] || Q.a[jj+1]!=P.a[jj+1]) mx=jj;
      k+="W"; for(long jj=0; jj<=mx+W && jj<(long)P.sep.size(); jj++) k+=to_string(P.sep[jj])+","; }
    string sh="S"+to_string(P.state)+"T"+to_string(sid(P.tail))+"R"+to_string(P.restid);
    return k+"#"+sh;
}
// predict the next increment from the automaton; false if any rule is missing or the activity is near the end of the chain
static long pf[10];
static bool predict(const MState& P, MState& Q){
    Q=P; size_t n=P.sep.size();
    if(cabad.count(cak(key0(P)))){ pf[0]++; return false; } auto it0=ca.find(key0(P)); if(it0==ca.end()){ pf[1]++; return false; } Q.a[0]+=it0->second.dv;
    for(size_t k=0;k<n;k++){
        CAkey kk=keyfor(P,Q,k); if(cabad.count(cak(kk))){ pf[2]++; return false; } auto it=ca.find(kk); if(it==ca.end()){ pf[3]++; return false; }
        Q.sep[k]=it->second.nw; Q.a[k+1]+=it->second.dv;
        if(k+3>=n && (Q.sep[k]!=P.sep[k] || it->second.dv!=0)){ pf[4]++; return false; }
    }
    auto e=exd.find(exshape(P)); if(e==exd.end()){ pf[5]++; return false; }
    for(size_t i=0;i<P.ex.size();i++){ Q.ex[i].c+=e->second[i]; if(Q.ex[i].c<60){ pf[6]++; return false; } }
    return true;
}
// cost of the unchanged separators: additive per separator id, g(id), known up to linear combinations
static set<size_t> keypos(const string& key){ set<size_t> r; size_t i=0; int bars=0; // positions listed in the key
    while(i<key.size()){ if(key[i]=='|'){ bars++; i++; if(bars>=2){ size_t j=i; while(j<key.size()&&isdigit(key[j])) j++; if(j<key.size()&&key[j]==':') r.insert(stoul(key.substr(i,j-i))); } continue; } i++; } return r; }
static map<int,int> gdiff(const CostModel& cm, const MState& P, const set<size_t>& kp){
    map<int,int> v; for(size_t j=0;j<P.sep.size();j++){ if(kp.count(j)) continue; v[P.sep[j]]++; v[cm.lsep[j]]--; }
    for(auto it=v.begin();it!=v.end();){ if(it->second==0) it=v.erase(it); else ++it; } return v;
}
struct GRow { map<int,long double> c; long double r; };
static vector<GRow> grref;   // reduced rows, pivot = first key
static void greduce(map<int,long double>& v, long double& r){
    for(auto& row: grref){ int pv=row.c.begin()->first; auto it=v.find(pv); if(it==v.end()) continue; long double f=it->second; for(auto& [k,x]: row.c){ v[k]-=f*x; if(fabsl(v[k])<1e-9) v.erase(k);} r-=f*row.r; }
}
static bool gknown(const map<int,int>& d, i128& val){
    map<int,long double> v; for(auto&[k,x]:d) v[k]=x; long double r=0; greduce(v,r); if(!v.empty()) return false;
    long double t=-r; long double rt=roundl(t); if(fabsl(t-rt)>1e-6) return false; val=(i128)rt; return true;
}
static long gadded=0;
static void gadd(const map<int,int>& d, i128 rhs){
    map<int,long double> v; for(auto&[k,x]:d) v[k]=x; long double r=(long double)rhs; greduce(v,r);
    if(v.empty()) return;
    int pv=v.begin()->first; long double f=v[pv]; for(auto& [k,x]: v) x/=f; r/=f;
    for(auto& row: grref){ auto it=row.c.find(pv); if(it==row.c.end()) continue; long double g=it->second; for(auto&[k,x]:v){ row.c[k]-=g*x; if(fabsl(row.c[k])<1e-9) row.c.erase(k);} row.r-=g*r; }
    grref.push_back({v,r}); gadded++;
}
static i128 evalbase(const CostModel& cm, const MState& P){
    i128 x=cm.c0; for(size_t k=0;k<P.a.size();k++) x+=cm.wl[k]*(2*P.a[k]+1)+cm.wp[k]*(P.a[k]&1); for(size_t i=0;i<P.ex.size();i++) x+=cm.we[i]*P.ex[i].c; return x;
}
// learn the cost model of key from state P (materialized in m); m is restored afterwards
static bool evalcost2(const CostModel& cm, const MState& P, const string& key, i128& out){
    i128 g; if(!gknown(gdiff(cm,P,keypos(key)),g)) return false; out=evalbase(cm,P)+g; return true;
}
static bool learn_cost(RSim& m, const MState& P, const string& key, i128 d0, long budget){
    TapeSnap T=snapof(m);
    CostModel cm; cm.wl.assign(P.a.size(),0); cm.wp.assign(P.a.size(),0); cm.we.assign(P.ex.size(),0);
    for(size_t k=0;k<P.a.size();k++){
        restoreto(m,T); m.R[levitem[k]].c+=4; i128 s0=m.steps;
        if(!oracle(m,budget)) { restoreto(m,T); return false; }
        i128 dd=m.steps-s0-d0; if(dd%4){ restoreto(m,T); return false; } cm.wl[k]=dd/4;
        restoreto(m,T); m.R[levitem[k]].c+=2; s0=m.steps;
        if(!oracle(m,budget)) { restoreto(m,T); return false; }
        i128 d1=m.steps-s0-d0-2*cm.wl[k]; cm.wp[k] = (P.a[k]&1)? -d1 : d1;
    }
    for(size_t i=0;i<P.ex.size();i++){
        restoreto(m,T); if(P.ex[i].side==0) m.L[P.ex[i].idx].c+=2; else m.R[P.ex[i].idx].c+=2; i128 s0=m.steps;
        if(!oracle(m,budget)) { restoreto(m,T); return false; }
        i128 dd=m.steps-s0-d0; if(dd%2){ restoreto(m,T); return false; } cm.we[i]=dd/2;
    }
    restoreto(m,T);
    CostModel z=cm; z.c0=0; cm.c0=d0-evalbase(z,P); cm.lsep=P.sep; cm.la=P.a; cm.ltail=P.tail; for(auto&e:P.ex) cm.lex.push_back(e.c);
    costs[key]=cm; return true;
}
struct ChainStats { long macro=0, oracle=0, learned=0, verified=0, entered=0, exits=0; };
static ChainStats cst;
// run the chain phase from a visit; returns when the phase cannot be continued in macro form (simulator state is exact)
// canonical polynomial hash of the whole tape (independent of how it is cut into items)
typedef unsigned long long u64; static const u64 HP=(1ULL<<61)-1, HB=1000003;
static u64 mulm(u64 a,u64 b){ __uint128_t r=(__uint128_t)a*b; u64 x=(u64)(r>>61)+(u64)(r&HP); return x>=HP? x-HP : x; }
static u64 powm(u64 a, unsigned __int128 e){ u64 r=1; while(e){ if(e&1) r=mulm(r,a); a=mulm(a,a); e>>=1; } return r; }
struct HS { u64 h=0, pw=1; unsigned __int128 len=0; };   // h = sum s_i B^i, pw = B^len
static void happ(HS& A, const string& w, i128 c){
    if(c<=0) return; HS W; for(char ch:w){ W.h=(W.h+mulm((u64)(ch-'0'),W.pw))%HP; W.pw=mulm(W.pw,HB); W.len++; }
    // sum_{j<c} W.h * W.pw^j  via doubling
    u64 sum=0, pk=1; HS R; // R = W^c
    u64 bh=W.h, bp=W.pw; unsigned __int128 bl=W.len; i128 e=c;
    u64 rh=0, rp=1; unsigned __int128 rl=0;
    while(e){ if(e&1){ rh=(rh+mulm(bh,rp))%HP; rp=mulm(rp,bp); rl+=bl; } bh=(bh+mulm(bh,bp))%HP; bp=mulm(bp,bp); bl*=2; e>>=1; }
    (void)sum;(void)pk;(void)R;
    A.h=(A.h+mulm(rh,A.pw))%HP; A.pw=mulm(A.pw,rp); A.len+=rl;
}
static string tapehash(RSim& m){   // right of head and left of head (read outwards); blanks hash to 0 so padding is invisible
    string bs=m.buf.str(0,m.buf.size()); long h=m.h; if(h<0) h=0; if(h>(long)bs.size()) h=bs.size();
    HS Rh; happ(Rh, bs.substr(h), 1); for(long k=(long)m.R.size()-1;k>=0;k--) happ(Rh,m.R[k].w,m.R[k].c);
    HS Lh; { string l=bs.substr(0,h); reverse(l.begin(),l.end()); happ(Lh,l,1); } for(long k=(long)m.L.size()-1;k>=0;k--){ string w=m.L[k].w; reverse(w.begin(),w.end()); happ(Lh,w,m.L[k].c); }
    char out[200]; snprintf(out,sizeof out,"R%016llx L%016llx state %c",(unsigned long long)Rh.h,(unsigned long long)Lh.h,'A'+m.s); return out;
}
static bool logexits = getenv("LOGEXITS")!=nullptr;
static void chain_phase(RSim& m, long verify, double deadline, chrono::steady_clock::time_point t0, long budget){
    MState P; if(!parse(m,P)) return;
    cst.entered++;
    bool dirty=false;   // P is ahead of the simulator's tape
    TapeSnap T;
    static double lastcp=0;
    while(true){
        double el=chrono::duration<double>(chrono::steady_clock::now()-t0).count(); if(el>=deadline) break;
        if(el-lastcp>=60 && (cst.macro+cst.oracle)%64==0){ lastcp=el; printf("  chain %8.1fs ofail %ld/%ld/%ld L %zu steps %s (10^%.3f) levels %zu a0 %s macro %ld oracle %ld costs %zu\n", el, ofail[0],ofail[1],ofail[2], m.L.size(), i2s(m.steps).c_str(), log10((double)m.steps), P.a.size(), i2s(P.a[0]).c_str(), cst.macro, cst.oracle, costs.size()); fflush(stdout); }
        MState Q; bool can=predict(P,Q);
        string key; CostModel* cm=nullptr;
        if(can){ key=costkey(P,Q); auto it=costs.find(key); if(it!=costs.end()) cm=&it->second; else { can=false; pf[7]++; } }
        i128 pc=0; bool gk=false;
        if(can){ gk=evalcost2(*cm,P,key,pc); if(!gk) pf[8]++; }
        if(can && gk && !(verify>0 && (cm->uses<verify))){
            m.steps+=pc; cm->uses++; P=Q; dirty=true; cst.macro++; continue;
        }
        // exact increment by the simulator
        if(dirty){ materialize(m,P); dirty=false; }
        else materialize(m,P);   // canonical itemization so that level items are known
        T=snapof(m); i128 s0=m.steps;
        if(!oracle(m,budget)){ restoreto(m,T); cst.exits++; if(logexits) printf("EXIT %s %s\n", i2s(m.steps).c_str(), tapehash(m).c_str()); return; }
        i128 d0=m.steps-s0; cst.oracle++;
        if(getenv("DUMPAT") && m.steps>(i128)atof(getenv("DUMPAT"))){ static int nd=0; if(nd++<8){ MState Qd; parse(m,Qd);
            printf("DUMP can %d gk %d key %s d0 %s pf:", can, gk, key.c_str(), i2s(d0).c_str()); for(int q=0;q<9;q++) printf(" %ld",pf[q]); printf("\n");
            auto pr=[&](const char* nm, MState& X){ printf(" %s a:",nm); for(auto x:X.a) printf(" %s",i2s(x).c_str()); printf("\n  sep:"); for(auto x:X.sep) printf(" [%s]",sepstr[x].c_str()); printf("\n  ex:"); for(auto&e:X.ex) printf(" %s",i2s(e.c).c_str()); printf("\n  tail %s\n  rest %s\n", X.tail.c_str(), X.rest.c_str()); };
            pr("P",P); pr("Q",Qd); fflush(stdout); } }
        MState Q2; bool pq=parse(m,Q2); if(getenv("WHYEXIT") && m.steps>(i128)atof(getenv("WHYEXIT")) && (!pq || !same_shape(P,Q2))){ static long nw=0; if(nw++<40){ printf("WHY parse %d", pq); if(pq) printf(" rest %d/%d nlev %zu/%zu nex %zu/%zu tail %d bidx %zu/%zu state %d/%d", P.restid==Q2.restid, 0, P.a.size(),Q2.a.size(),P.ex.size(),Q2.ex.size(), P.tail==Q2.tail, P.bidx,Q2.bidx,P.state,Q2.state); printf("\n  P.rest %s\n  Q.rest %s\n", P.rest.c_str(), Q2.rest.c_str()); } }
        if(!pq || !same_shape(P,Q2)){ cst.exits++; if(logexits) printf("EXIT %s %s\n", i2s(m.steps).c_str(), tapehash(m).c_str()); return; }
        if(can && cm && !gk){   // separator costs not yet determined: one more equation
            bool ok = Q2.a==Q.a && Q2.sep==Q.sep;
            if(ok){ gadd(gdiff(*cm,P,keypos(key)), d0-evalbase(*cm,P)); }
        } else if(can && cm){   // verification of a known prediction
            bool ok = pc==d0 && Q2.a==Q.a && Q2.sep==Q.sep;
            for(size_t i=0;i<Q.ex.size() && ok;i++) ok = Q.ex[i].c==Q2.ex[i].c;
            if(!ok){ auto pr=[&](const char*nm,const vector<int>&sp,const vector<i128>&a,const vector<i128>&ex,const string&tl){ fprintf(stderr,"%s a:",nm); for(auto x:a) fprintf(stderr," %s",i2s(x).c_str()); fprintf(stderr,"\n sep:"); for(auto x:sp) fprintf(stderr," [%s]",sepstr[x].c_str()); fprintf(stderr,"\n ex:"); for(auto x:ex) fprintf(stderr," %s",i2s(x).c_str()); fprintf(stderr,"\n tail %s\n",tl.c_str()); }; vector<i128> pe; for(auto&e:P.ex) pe.push_back(e.c); pr("NOW",P.sep,P.a,pe,P.tail); pr("LEARNED",cm->lsep,cm->la,cm->lex,cm->ltail); fprintf(stderr," wl:"); for(auto x:cm->wl) fprintf(stderr," %s",i2s(x).c_str()); fprintf(stderr,"\n we:"); for(auto x:cm->we) fprintf(stderr," %s",i2s(x).c_str()); fprintf(stderr,"\n"); fprintf(stderr,"VERIFY MISMATCH at steps %s key %s: predicted %s actual %s\n", i2s(s0).c_str(), key.c_str(), i2s(pc).c_str(), i2s(d0).c_str()); exit(4); }
            cm->uses++; cst.verified++;
        } else {
            if(!learn_ca(P,Q2)){ P=Q2; continue; }
            string k2=costkey(P,Q2);
            if(!costs.count(k2)){
                TapeSnap after=snapof(m); restoreto(m,T);
                bool ok=learn_cost(m,P,k2,d0,budget);
                restoreto(m,after);
                if(ok) cst.learned++;
            }
        }
        P=Q2;
    }
    if(dirty) materialize(m,P);
}

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
    if(mode=="visits"){   // visits T0 N TMAX: the tape at the first N left-end samples after step T0
        sim.visit_from=strtold(argv[3],nullptr); sim.visit_n=atol(argv[4]); if(getenv("MAXL")) sim.visit_maxL=atol(getenv("MAXL")); if(getenv("MAXITEMS")) sim.visit_maxitems=atol(getenv("MAXITEMS"));
        vector<i128> sched={1000000,10000000,100000000,1000000000,3000000000LL,10000000000LL}; i128 tmax=(i128)strtold(argv[5],nullptr);
        i128 t=sched[0]; size_t si=0;
        while(sim.steps<tmax && sim.visit_n>0){ if(!sim.run(t<tmax?t:tmax)) break; si++; t = si<sched.size()? sched[si] : t*10; }
        return 0;
    }
    if(mode=="turns"){   // turns T0 T1: histogram of left turns by number of left-rope items, between T0 and T1
        sim.visit_from=strtold(argv[3],nullptr); sim.turnhist=true; i128 tmax=(i128)strtold(argv[4],nullptr);
        vector<i128> sched={1000000,10000000,100000000,1000000000,3000000000LL,10000000000LL}; i128 t=sched[0]; size_t si=0;
        while(sim.steps<tmax){ if(!sim.run(t<tmax?t:tmax)) break; si++; t = si<sched.size()? sched[si] : t*10; }
        long tot=0; for(auto x:sim.th) tot+=x; printf("steps %s turns %ld rules %ld items %zu\n", i2s(sim.steps).c_str(), tot, sim.nrule, sim.nitems());
        for(size_t k=0;k<sim.th.size();k++) if(sim.th[k]) printf("%zu %ld\n",k,sim.th[k]);
        return 0;
    }
    if(mode=="chain"){   // chain TMAX SECONDS [VERIFY]: decades run, chain phases in macro form
        i128 tmax=(i128)strtold(argv[3],nullptr); double secs=atof(argv[4]); long verify = argc>5? atol(argv[5]) : 2;
        auto t0=chrono::steady_clock::now(); sim.t0=t0; sim.deadline=secs;
        vector<i128> sched={1000000,10000000,100000000,1000000000,3000000000LL,10000000000LL}; i128 t=sched[0]; size_t si=0;
        sim.stop_at_visit=true; long budget=2000000; double lastp=-100;
        while(sim.steps<tmax){
            i128 tt=t<tmax?t:tmax;
            if(!sim.run(tt)){ printf("HALT %s\n", i2s(sim.steps).c_str()); break; }
            if(sim.timeout || sim.memout) break;
            if(sim.buf.size()==0 && sim.is_incr()){ chain_phase(sim,verify,secs,t0,budget); }
            if(sim.steps>=t){ si++; t = si<sched.size()? sched[si] : t*10; }
            double e=chrono::duration<double>(chrono::steady_clock::now()-t0).count();
            if(e-lastp>=30){ lastp=e; printf("%9.1fs steps %s (10^%.3f) items %zu jumps %ld macro %ld oracle %ld learned %ld verified %ld phases %ld ca %zu costs %zu conflicts %ld geq %ld\n", e, i2s(sim.steps).c_str(), log10((double)sim.steps), sim.nitems(), sim.njumps, cst.macro, cst.oracle, cst.learned, cst.verified, cst.entered, ca.size(), costs.size(), ca_conflicts, gadded); fflush(stdout); }
            if(e>secs) break;
        }
        printf("predict fails:"); for(int q=0;q<9;q++) printf(" %ld",pf[q]); printf(" oracle fails %ld %ld %ld",ofail[0],ofail[1],ofail[2]); printf(" exits %ld\n", cst.exits);
        printf("FINAL steps %s (10^%.3f) macro %ld oracle %ld learned %ld verified %ld phases %ld conflicts %ld\n", i2s(sim.steps).c_str(), log10((double)sim.steps), cst.macro, cst.oracle, cst.learned, cst.verified, cst.entered, ca_conflicts);
        return 0;
    }
    if(mode=="edit"){   // edit T variant...: variant = comma list of aK=V / sK=0|1|2|3 ; "-" = unchanged
        vector<i128> sched={1000000,10000000,100000000,1000000000,3000000000LL,10000000000LL}; i128 T0=(i128)strtold(argv[3],nullptr);
        i128 t=sched[0]; size_t si=0;
        while(sim.steps<T0){ i128 tt=t<T0?t:T0; if(!sim.run(tt)) return 1; if(sim.steps>=t){ si++; t = si<sched.size()? sched[si] : t*10; } }
        sim.jumps=false; sim.stop_at_visit=true; sim.run((i128)1e36L);
        MState P; if(!parse(sim,P)){ printf("noparse\n"); return 1; }
        int ids[4]={sid("100100100"),sid("11100"),sid("10"),sid("1010")};
        printf("visit %s a:",i2s(sim.steps).c_str()); for(auto x:P.a) printf(" %s",i2s(x).c_str()); printf(" seps:"); for(auto x:P.sep) printf(" [%s]",sepstr[x].c_str()); printf("\n");
        materialize(sim,P); TapeSnap T=snapof(sim);
        for(int v=4; v<argc; v++){
            MState P2=P; string e=argv[v];
            if(e!="-"){ stringstream ss(e); string tok; while(getline(ss,tok,',')){ int k=atoi(tok.c_str()+1); long val=atol(tok.c_str()+tok.find('=')+1); if(tok[0]=='a') P2.a[k]=val; else P2.sep[k]=ids[val]; } }
            restoreto(sim,T); materialize(sim,P2); i128 s1=sim.steps;
            if(!oracle(sim,4000000)){ printf("%s F\n",e.c_str()); continue; }
            MState Q; parse(sim,Q); printf("%-30s cost %s  Q.a:",e.c_str(),i2s(sim.steps-s1).c_str()); for(auto x:Q.a) printf(" %s",i2s(x).c_str()); printf("\n");
        }
        return 0;
    }
    if(mode=="flip"){   // flip T NV: at NV increment visits after T, cost change when one separator D0D0D0 <-> D1 is swapped
        vector<i128> sched={1000000,10000000,100000000,1000000000,3000000000LL,10000000000LL}; i128 T0=(i128)strtold(argv[3],nullptr);
        i128 t=sched[0]; size_t si=0;
        while(sim.steps<T0){ i128 tt=t<T0?t:T0; if(!sim.run(tt)) return 1; if(sim.steps>=t){ si++; t = si<sched.size()? sched[si] : t*10; } }
        sim.jumps=false; sim.stop_at_visit=true; sim.run((i128)1e36L);
        int NV=atoi(argv[4]); int A=sid("100100100"), B=sid("11100");
        for(int v=0; v<NV; v++){
            MState P; if(!parse(sim,P)){ printf("noparse\n"); sim.run((i128)1e36L); continue; }
            materialize(sim,P); TapeSnap T=snapof(sim); i128 s0=sim.steps;
            if(!oracle(sim,2000000)){ printf("oracle fail\n"); return 1; } i128 d0=sim.steps-s0; MState Q; parse(sim,Q); TapeSnap after=snapof(sim);
            printf("visit %s d0 %s n %zu seps", i2s(s0).c_str(), i2s(d0).c_str(), P.sep.size()); for(auto x:P.sep) printf(" %s", x==A?"0":x==B?"1":"x"); printf(" |");
            for(size_t j=0;j<P.sep.size();j++){
                if(P.sep[j]!=A && P.sep[j]!=B) continue;
                MState P2=P; P2.sep[j]= P.sep[j]==A? B:A; restoreto(sim,T); materialize(sim,P2); i128 s1=sim.steps;
                if(!oracle(sim,2000000)){ printf(" %zu:F",j); continue; } MState Q2; parse(sim,Q2);
                bool same = Q2.a.size()==Q.a.size();
                printf(" %zu:%s%s",j,i2s(sim.steps-s1-d0).c_str(), same?"":"*");
            }
            printf("\n"); fflush(stdout);
            restoreto(sim,after);
        }
        return 0;
    }
    if(mode=="probe"){   // probe T0 NV: at NV consecutive increment visits after T0, coefficients of the step cost
        vector<i128> sched={1000000,10000000,100000000,1000000000,3000000000LL,10000000000LL}; i128 T0=(i128)strtold(argv[3],nullptr);
        i128 t=sched[0]; size_t si=0;
        while(sim.steps<T0){ i128 tt=t<T0?t:T0; if(!sim.run(tt)) return 1; if(sim.steps>=t){ si++; t = si<sched.size()? sched[si] : t*10; } }
        sim.jumps=false; sim.stop_at_visit=true;
        sim.run((i128)1e36L);   // to the next increment visit
        int NV=atoi(argv[4]); int delta = getenv("DELTA")? atoi(getenv("DELTA")) : 2;
        for(int v=0; v<NV; v++){
            RSim base=sim; i128 s0=base.steps; base.run((i128)1e36L); i128 d0=base.steps-s0;
            printf("visit %s d0 %s |", i2s(s0).c_str(), i2s(d0).c_str());
            for(int side=0; side<2; side++){
                Rope& rp = side==0? sim.L : sim.R;
                for(size_t k=0;k<rp.size();k++){
                    if(rp[k].c<50) continue;
                    RSim c=sim; Rope& cr = side==0? c.L : c.R; cr[k].c += delta;
                    i128 c0=c.steps; c.run((i128)1e36L); i128 dd=c.steps-c0;
                    printf(" %c%zu:%s^%s:%s", side?'R':'L', side? rp.size()-1-k : k, rp[k].w.substr(0,12).c_str(), i2s(rp[k].c).c_str(), i2s(dd-d0).c_str());
                }
            }
            printf("\n"); fflush(stdout);
            sim=base;
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
