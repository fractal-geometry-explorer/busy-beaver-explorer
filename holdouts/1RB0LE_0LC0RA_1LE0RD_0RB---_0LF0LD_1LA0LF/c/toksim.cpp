// toksim: fast simulator of the rounds S_{k+1} = 1 0 A(S_k) of 1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF
// (mirrored tape; the twin 1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC--- has the same rounds, see the README).
// Same token rules as py/tokz.py (words L = 1010, O = 000, I = 100, defects x = 10, 1, z = 0), and the same
// tape after every round (checked token for token against py/tokz.py at round 3,000 and against the plain
// version of this engine at rounds 8,000 and 30,000).
//
// What makes it fast:
//  * a carry (a number of visits of A) is a run-length coded bit string, lowest bit first, so a doubler,
//    a digit or a defect step costs O(1) whatever the size of the carry, and a run of L's is skipped at once;
//  * the digit-only end of the tape is kept as a machine-word bit array, and a carry that reaches it is
//    added in one big-number addition;
//  * once the round's defect has died, all carries still on their way are walked to the end together
//    (in a tape without defects carries commute), merged in a dense bit array.
// A round then costs about O(length of the tape): 100,000 rounds take about 2 minutes, 10^6 about 4 hours.
//
// usage: toksim ROUNDS [EVERY=10000] [DUMP_ROUND] [RECORD_FILE]
//   prints a line every EVERY rounds and every round in which the defect did not end at 1 I O -> O L;
//   stops with "TWO DEFECTS MEET" if a token rule would need two defects next to each other (the only
//   way a halt can start). DUMP_ROUND: writes that round's starting tape to dump.txt. RECORD_FILE: writes
//   for every round four int32s: k, |Z| (length of the digit-only end at the start of the round), e (where
//   the defect died minus where Z started, INT_MIN if it did not die), the kind of death (0 = 1 I O -> O L).
//   Summary columns: reach = share of rounds (from 100 on) whose defect got into Z, loss/round = words of Z
//   eaten per round (Z gains 4), maxe = most words of Z eaten in one round, minmargin = smallest
//   |Z| - (k + 2 log2 k + 20), log2carry = bits of the largest carry of the round (the round takes at
//   least 2^log2carry machine steps), crossings = defect steps in the round.
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;

struct Bits { // n >= 0 as runs (bit, length), bottom first; top run is always a 1-run
  deque<pair<char,ll>> r; ll total=0;
  bool zero() const { return r.empty(); }
  void norm_top(){ while(!r.empty() && r.back().first==0){ total-=r.back().second; r.pop_back(); } }
  void push_bottom(char b, ll len){ if(len<=0) return; if(!r.empty() && r.front().first==b) r.front().second+=len; else r.emplace_front(b,len); total+=len; }
  char pop_bottom(){ // remove lowest bit (n>>=1), return it
    if(r.empty()) return 0;
    char b=r.front().first; if(--r.front().second==0) r.pop_front(); total--; return b; }
  void shl(ll s){ if(!r.empty()) push_bottom(0,s); }
  void set_pow2(ll m){ r.clear(); total=0; r.emplace_back(1,1); total=1; push_bottom(0,m); }
  void set_one(){ set_pow2(0); }
  void inc(){
    if(r.empty()){ r.emplace_back(1,1); total=1; return; }
    if(r.front().first==0){ // ...0 -> ...1
      pop_bottom(); push_bottom(1,1); return; }
    ll len=r.front().second; r.pop_front(); total-=len; // 1^len -> 0^len then +1 above
    if(r.empty()){ r.emplace_front(1,1); total+=1; } else { // next run is 0s
      pop_bottom(); push_bottom(1,1); }
    push_bottom(0,len);
  }
  void dec(){ // n>0
    if(r.front().first==1){ pop_bottom(); push_bottom(0,1); norm_top(); return; }
    ll len=r.front().second; r.pop_front(); total-=len; // 0^len 1.. -> 1^len 0..
    pop_bottom(); push_bottom(0,1); norm_top();
    // the borrowed bit: we removed bottom 1 of next run and put a 0 there
    push_bottom(1,len); norm_top();
  }
};


// a+b for run-length carries
Bits addb(const Bits&a,const Bits&b){
  Bits o; size_t ia=0, ib=0; ll ra=0, rb=0; // remaining in current runs
  char xa=0,xb=0; int c=0;
  auto push=[&](char bit,ll len){ if(len<=0) return; if(!o.r.empty()&&o.r.back().first==bit) o.r.back().second+=len; else o.r.emplace_back(bit,len); o.total+=len; };
  while(true){
    if(ra==0){ if(ia<a.r.size()){ xa=a.r[ia].first; ra=a.r[ia].second; ia++; } else { xa=0; ra=-1; } }
    if(rb==0){ if(ib<b.r.size()){ xb=b.r[ib].first; rb=b.r[ib].second; ib++; } else { xb=0; rb=-1; } }
    if(ra<0 && rb<0){ if(c) push(1,1); break; }
    ll L = ra<0? rb : (rb<0? ra : min(ra,rb));
    int s=xa+xb;
    if(s==0){ if(c){ push(1,1); push(0,L-1); c=0; } else push(0,L); }
    else if(s==1){ if(c) push(0,L); else push(1,L); }
    else { if(c) push(1,L); else { push(0,1); push(1,L-1); c=1; } }
    if(ra>0) ra-=L;
    if(rb>0) rb-=L;
  }
  o.norm_top(); return o;
}

// The carry walked by flush(), as a dense bit array in absolute coordinates: bit `base` is its lowest bit.
struct Dense {
  vector<unsigned long long> w; ll base=0, ones=0, top=0; // top: an upper bound (exclusive) of set bits
  void reset(ll nbits, ll b0){ ll nl=nbits/64+4; if((ll)w.size()<nl) w.assign(nl,0); base=b0; ones=0; top=b0; }
  inline int get(ll p) const { return (w[p>>6]>>(p&63))&1; }
  inline void flip(ll p){ w[p>>6]^=1ULL<<(p&63); }
  bool zero() const { return ones==0; }
  int pop_bottom(){ int b=get(base); if(b){ flip(base); ones--; } base++; if(top<base) top=base; return b; }
  void shl(ll r){ base-=r; }
  void inc(){ ll p=base; while(get(p)){ flip(p); ones--; p++; } flip(p); ones++; if(p+1>top) top=p+1; }
  // add the runs of n with its lowest bit at base
  void add(const Bits&n){
    ll p=base;
    for(auto&r:n.r){ if(r.first){ addones(p,r.second); } p+=r.second; }
    if(p+1>top) top=p+1;
  }
  void addones(ll p, ll len){ // += (2^len - 1) << p, i.e. += 2^(p+len) - 2^p
    addpow(p+len); subpow(p); }
  void addpow(ll p){ ll li=p>>6; unsigned long long add=1ULL<<(p&63);
    while(true){ unsigned long long old=w[li]; unsigned long long nw=old+add; ones+=__builtin_popcountll(nw)-__builtin_popcountll(old); w[li]=nw; if(nw>=old) break; add=1; li++; }
    if(li*64+64>top) top=li*64+64; }
  void subpow(ll p){ ll li=p>>6; unsigned long long sub=1ULL<<(p&63);
    while(true){ unsigned long long old=w[li]; unsigned long long nw=old-sub; ones+=__builtin_popcountll(nw)-__builtin_popcountll(old); w[li]=nw; if(nw<=old) break; sub=1; li++; } }
  ll bits() const { ll t=top; while(t>base && !get(t-1)) t--; return t-base; }
} D;
struct Pend { ll pos; Bits n; };
vector<Pend> pend; bool dead=false; ll alive=0;
vector<char> T; // tokens L O I x 1 z, followed by the digits in Z
// Z: the digit-only end of the tape, from index T.size() on, as a bit string (bit j = digit j, 1 = I).
struct ZStore {
  vector<unsigned long long> w; ll off=0; ll len=0; // digit j is bit off+j of w
  void init(){ w.assign(1<<12,0); off=(ll)(1<<11)*64; len=0; }
  void ensure_top(ll bits){ ll need=(off+bits)/64+2; if((ll)w.size()<need) w.resize(max<ll>(need,(ll)w.size()*2),0); }
  int get(ll j) const { ll b=off+j; return (w[b>>6]>>(b&63))&1; }
  void setbit(ll j,int v){ ll b=off+j; if(v) w[b>>6]|=1ULL<<(b&63); else w[b>>6]&=~(1ULL<<(b&63)); }
  // pop c low digits (c<=len)
  void pop_low(ll c){ for(ll j=0;j<c;j++) setbit(j,0); off+=c; len-=c; }
  void push_low(int v){ if(off==0) recenter(); off--; len++; setbit(0,v); }
  void recenter(){ vector<unsigned long long> nw(w.size()*2,0); ll sh=(ll)w.size()*64; // shift up by sh bits (limb aligned)
     for(size_t i=0;i<w.size();i++) nw[i+w.size()]=w[i];
     w.swap(nw); off+=sh; }
  // add n (runs, bottom first) at digit 0
  void add(const Bits&n){
    ensure_top(max(len,n.total)+2);
    ll pos=off; ll firstlimb=off>>6; ll lastlimb=firstlimb;
    // add each 1-run as (2^(a+len)-2^a) via limb-wise adds with carry: build addend limbs on the fly
    // simpler: build addend in a temp buffer
    static vector<unsigned long long> tmp; ll nl=(n.total+ (off&63))/64+2; tmp.assign(nl,0);
    ll b=off&63;
    for(auto&r:n.r){ if(r.first){ ll a=b, e=b+r.second; // set bits [a,e)
        while(a<e){ ll li=a>>6, bi=a&63; ll take=min<ll>(64-bi,e-a); unsigned long long m= (take==64)?~0ULL:(((1ULL<<take)-1)<<bi); tmp[li]|=m; a+=take; } }
      b+=r.second; }
    unsigned long long c=0; ll i;
    for(i=0;i<nl;i++){ unsigned long long x=w[firstlimb+i]; unsigned __int128 s=(unsigned __int128)x+tmp[i]+c; w[firstlimb+i]=(unsigned long long)s; c=(unsigned long long)(s>>64); }
    while(c){ ensure_top((firstlimb+i+1)*64-off+64); unsigned __int128 s=(unsigned __int128)w[firstlimb+i]+c; w[firstlimb+i]=(unsigned long long)s; c=(unsigned long long)(s>>64); i++; }
    lastlimb=firstlimb+i;
    // new length: max(len, bitlength of value)
    ll top=-1; for(ll li=lastlimb+1; li>=firstlimb; li--){ if(li<(ll)w.size() && w[li]){ top=li*64+63-__builtin_clzll(w[li]); break; } }
    if(top>=off) len=max(len, top-off+1);
  }
  void addDense(const Dense&D, ll nb);
  ll bitlen() const {
    if(len==0) return 0; ll hi=off+len-1; ll li=hi>>6; ll lo=off>>6;
    for(;li>=lo;li--){ unsigned long long x=w[li];
      if(li==(hi>>6) && (hi&63)!=63) x&=((1ULL<<((hi&63)+1))-1);
      if(li==lo) x&=~((1ULL<<(off&63))-1);
      if(x){ ll hb=li*64+63-__builtin_clzll(x); return hb-off+1; } }
    return 0; }
} Z;

struct Die { int kind; ll pos; }; // 0 IO, 1 x-end, 2 1-end, 3 Eh-end, 4 E0-end
vector<Die> dies; ll maxbits=0; ll ncross=0;
[[noreturn]] void adj(const char*w, ll i){
  fprintf(stdout,"TWO DEFECTS MEET (%s) at token %lld of %zu\n",w,i,T.size()); fflush(stdout); exit(2);}

static inline ll skipL(ll i, ll lim){ // first index >= i, < lim, with T[i] != 'L' (or lim)
  const unsigned long long LL8=0x4C4C4C4C4C4C4C4CULL; const char*p=T.data();
  while(i+8<=lim){ unsigned long long w; memcpy(&w,p+i,8); w^=LL8; if(w){ return i+(__builtin_ctzll(w)>>3); } i+=8; }
  while(i<lim && p[i]=='L') i++; return i; }
void An(Bits &n, ll i);
void ZStore::addDense(const Dense&Dd, ll nb){
  Bits tmpb; // build runs from the dense bits (cost nb/64 + runs)
  ll p=Dd.base, e=Dd.base+nb; 
  while(p<e){ int b=Dd.get(p); ll q=p; // find end of run
    while(q<e){ if(((q&63)==0) && q+64<=e){ unsigned long long x=Dd.w[q>>6]; if((b && x==~0ULL)||(!b && x==0)){ q+=64; continue; } }
      if(Dd.get(q)!=b) break; q++; }
    tmpb.r.emplace_back((char)b,q-p); tmpb.total+=q-p; p=q; }
  tmpb.norm_top(); if(!tmpb.zero()) add(tmpb); }
ll nmat=0;
bool more(){ // move up to 64 low digits of Z into T; false if Z is empty
  if(Z.len==0) return false; ll c=min<ll>(64,Z.len);
  for(ll j=0;j<c;j++) T.push_back(Z.get(j)?'I':'O'); Z.pop_low(c); nmat+=c; return true; }
void absorb(){ // give trailing digits of T back to Z, keeping 64
  ll sz=T.size(), j=sz; while(j>0 && (T[j-1]=='O'||T[j-1]=='I')) j--;
  ll give=(sz-j)-64; if(give<=0) return;
  for(ll t=sz-1;t>=sz-give;t--) Z.push_low(T[t]=='I');
  T.resize(sz-give); }
void Eh(ll i){
  while(true){
    if(i==(ll)T.size() && more()) continue;
    if(i==(ll)T.size()){ T.push_back('I'); dies.push_back({3,i}); if(--alive==0) dead=true; return; }
    char t=T[i];
    if(t=='L'){ i=skipL(i,T.size()); continue; }
    if(t=='O'){ T[i]='1'; return; }
    if(t=='I') break;
    adj("Eh",i);
  }
  ll j=i; // T[j]=='I', erased in the rules; look at T[j+1]
  if(j+1==(ll)T.size()) more();
  if(j+1==(ll)T.size()){ T[j]='L'; dies.push_back({4,j}); if(--alive==0) dead=true; return; }
  char u=T[j+1];
  if(u=='O'){ T[j]='L'; T.erase(T.begin()+j+1); dies.push_back({0,j}); if(--alive==0) dead=true; return; }
  if(u=='L'){ T[j]='O'; T[j+1]='x'; Bits one; one.set_one(); An(one,j+1); return; }
  if(u=='I'){ T[j]='O'; T[j+1]='1'; return; }
  adj("E0",j);
}
void An(Bits &n, ll i){
  while(!n.zero()){
    if(dead){ pend.push_back({i,n}); return; }
    if(n.total>maxbits) maxbits=n.total;
    if(i==(ll)T.size()){ Z.add(n); return; }
    char t=T[i];
    if(t=='L'){ // skip a run of L's at once
      ll j=skipL(i,T.size());
      n.shl(j-i); i=j; continue; }
    if(t=='O'){ char b=n.pop_bottom(); T[i]= b?'I':'O'; i++; continue; }
    if(t=='I'){ char b=n.pop_bottom(); T[i]= b?'O':'I'; if(b) n.inc(); i++; continue; }
    if(t=='z'){ T[i]='1'; n.dec(); continue; }
    if(t=='x'){
      ncross++;
      if(i+1==(ll)T.size()) more();
      if(i+1==(ll)T.size()){ T[i]='I'; dies.push_back({1,i}); if(--alive==0) dead=true; continue; }
      char u=T[i+1];
      if(u=='O'){ T[i]='O'; T[i+1]='x'; n.dec(); continue; }
      if(u=='I'){ T[i]='L'; T[i+1]='O'; Eh(i+2); n.dec(); continue; }
      if(u=='L'){ T[i]='L'; T[i+1]='x'; i++; n.shl(1); continue; }
      adj("x",i);
    }
    if(t=='1'){
      ncross++;
      if(i+1==(ll)T.size()) more();
      if(i+1==(ll)T.size()){ T[i]='I'; dies.push_back({2,i}); if(--alive==0) dead=true; continue; }
      T[i]='O'; Eh(i+1); n.dec(); continue; }
    adj("?",i);
  }
}

void flush(){ // all carries left after the defect died: walk them together to Z, merging on the way
  if(pend.empty()) return;
  sort(pend.begin(),pend.end(),[](const Pend&a,const Pend&b){return a.pos<b.pos;});
  ll maxtot=0; for(auto&p:pend) maxtot=max(maxtot,p.n.total);
  ll span=(ll)T.size()+Z.len+maxtot+256;
  D.reset(3*span, span); // base starts in the middle: it moves down at most span (L's), up at most span
  size_t q=0; ll i=pend[0].pos;
  while(true){
    while(q<pend.size() && pend[q].pos<=i){ D.add(pend[q].n); q++; }
    if(D.zero()){ if(q==pend.size()) break; i=pend[q].pos; continue; }
    ll sz=T.size();
    if(i>=sz){ while(q<pend.size()){ D.add(pend[q].n); q++; }
      ll nb=D.bits(); if(nb>maxbits) maxbits=nb; Z.addDense(D, nb); break; }
    char t=T[i];
    if(t=='L'){ ll lim = q<pend.size()? min<ll>(sz,pend[q].pos) : sz; ll j=skipL(i,lim); D.shl(j-i); i=j; continue; }
    if(t=='O'){ int b=D.pop_bottom(); T[i]= b?'I':'O'; i++; continue; }
    if(t=='I'){ int b=D.pop_bottom(); T[i]= b?'O':'I'; if(b) D.inc(); i++; continue; }
    adj("flush",i);
  }
  // clear what is left of D
  if(!D.zero()){ for(ll li=D.base>>6; li*64<D.top+64 && li<(ll)D.w.size(); li++) D.w[li]=0; D.ones=0; }
  pend.clear();
}
void norm(){
  size_t i=1; while(i<T.size() && T[i]=='L') i++;
  for(size_t j=1;j<i;j++) T[j-1]='L';
  T[i-1]='x';
  if(i<T.size() && T[i]=='I'){ T[i-1]='L'; T[i]='z'; }
  else if(i<T.size() && (T[i]=='x'||T[i]=='1'||T[i]=='z')) adj("front",i);
}
int main(int argc,char**argv){
  if(argc<2){ fprintf(stderr,"usage: toksim ROUNDS [EVERY] [DUMP_ROUND] [RECORD_FILE]\n"); return 1; }
  ll R=atoll(argv[1]); ll EVERY=argc>2?atoll(argv[2]):10000; ll DUMP=argc>3?atoll(argv[3]):-1;
  const char*s0="LLLzLLOLOI"; T.assign(s0,s0+strlen(s0)); T.reserve(5*R+100); Z.init();
  ll reach=0, cnt=0; double losssum=0; ll maxe=-1, maxe_k=0;
  double minmargin=1e18; ll minmargin_k=0; double minzk=1e9; ll minzk_k=0;
  ll lastreach=0, lr_runmax=0, lr_run=0;
  // checkpoints: TOKSIM_CKPT=FILE writes the tape every TOKSIM_CKPT_EVERY rounds (default 50,000);
  // TOKSIM_RESUME=FILE starts from such a file (the record file is then appended to)
  const char*ck=getenv("TOKSIM_CKPT"); ll CKE=getenv("TOKSIM_CKPT_EVERY")?atoll(getenv("TOKSIM_CKPT_EVERY")):50000;
  ll k0=6; const char*rs=getenv("TOKSIM_RESUME");
  if(rs){ FILE*f=fopen(rs,"r"); if(!f){ fprintf(stderr,"cannot read %s\n",rs); return 1; }
    ll kk; if(fscanf(f,"%lld\n",&kk)!=1) return 1; T.clear(); int c;
    while((c=fgetc(f))!=EOF && c!='\n') T.push_back((char)c);
    fclose(f); absorb(); k0=kk+1; printf("resumed at round %lld, %zu tokens + %lld digits\n",k0,T.size(),Z.len); }
  auto t0=chrono::steady_clock::now(); FILE*rec=argc>4?fopen(argv[4],rs?"ab":"wb"):nullptr;
  for(ll k=k0;k<=R;k++){
    ll sz=T.size(), zs=sz; while(zs>0 && (T[zs-1]=='O'||T[zs-1]=='I')) zs--;
    ll zlen=sz-zs+Z.len;
    dies.clear(); maxbits=0; ncross=0;
    alive=0; for(char c:T) if(c=='x'||c=='1'||c=='z') alive++; dead=false; Bits one; one.set_one(); An(one,0); flush();
    T.insert(T.begin(),'x'); norm();
    Z.len=Z.bitlen(); if(Z.len==0) while(!T.empty() && T.back()=='O') T.pop_back();
    absorb();
    ll nm=0; // markers: the round's new defect only (scan cheap region? count all)
    bool usual = dies.size()==1 && dies[0].kind==0;
    if(!usual){
      printf("round %lld: unusual end of the defect:",k); for(auto&d:dies) printf(" (%d,%lld)",d.kind,d.pos);
      printf(" len %zu\n",T.size()); fflush(stdout);
    }
    if(k>=100 && !dies.empty()){
      ll e=dies[0].pos - zs; cnt++;
      if(e>=0){ reach++; losssum+=e+2; if(e>maxe){maxe=e;maxe_k=k;} lr_run++; lr_runmax=max(lr_runmax,lr_run);} else lr_run=0;
      double lg=log2((double)k); double margin=zlen-(k+2*lg+20);
      if(margin<minmargin){minmargin=margin;minmargin_k=k;}
      if((double)zlen/k<minzk){minzk=(double)zlen/k;minzk_k=k;}
    }
    if(rec){ int rr[4]={(int)k,(int)zlen,dies.empty()?INT_MIN:(int)(dies[0].pos-zs),dies.empty()?-1:dies[0].kind}; fwrite(rr,4,4,rec); if(k%EVERY==0) fflush(rec); }
    if(ck && k%CKE==0){ string tmp=string(ck)+".tmp"; FILE*f=fopen(tmp.c_str(),"w"); fprintf(f,"%lld\n",k);
      fwrite(T.data(),1,T.size(),f); for(ll j=0;j<Z.len;j++) fputc(Z.get(j)?'I':'O',f); fputc('\n',f); fclose(f);
      rename(tmp.c_str(),ck); if(rec) fflush(rec); }
    if(k==DUMP){ FILE*f=fopen("dump.txt","w"); fwrite(T.data(),1,T.size(),f); for(ll j=0;j<Z.len;j++) fputc(Z.get(j)?'I':'O',f); fputc('\n',f); fclose(f); }
    if(k%EVERY==0){
      double el=chrono::duration<double>(chrono::steady_clock::now()-t0).count();
      printf("k %lld len %lld |Z| %lld |Z|/k %.4f die@%lld (Z starts %lld) reach %.4f loss/round %.3f maxe %lld@%lld minmargin %.0f@%lld log2carry %lld crossings %lld t %.0fs\n",
        k,(ll)T.size()+Z.len,zlen,(double)zlen/k,dies.empty()?-1:dies[0].pos,zs,(double)reach/cnt,losssum/cnt,maxe,maxe_k,minmargin,minmargin_k,maxbits,ncross,el);
      fflush(stdout);
    }
  }
  printf("DONE %lld rounds, no two defects ever met; every round's defect ended at 1 I O -> O L unless listed above\n",R);
  printf("rounds 100..%lld: reach %lld of %lld (%.4f), mean loss %.4f, max e %lld (round %lld), longest run of reaching rounds %lld, min |Z|-(k+2log2k+20) = %.0f (round %lld), min |Z|/k %.4f (round %lld)\n",
    R,reach,cnt,(double)reach/cnt,losssum/cnt,maxe,maxe_k,lr_runmax,minmargin,minmargin_k,minzk,minzk_k);
}
