// vispl.c: c/visps.c plus a log of the right end of every round, for lean/Shift.lean and py/dirty_counts.py.
// Each round writes one line to $VLOG (default v.log): R round F stop d dirty W the 96 cells from F-48 after the round
// V the blocks it handled from the previous stop minus 48 on, as offset:visits (offsets from the previous round's stop).
// gcc -O2 -o vispl c/vispl.c -lpthread; VLOG=v1m.log ./vispl MACHINE 1000001 - 3 100000
//
// visps.c: c/visp.c plus a record of every round's stop (the last block its cascade reaches), for lean/Cascade.lean.
// Prints, for each visit to 1011, its cell and the previous round's stop F (the theorem says cell >= F - 2), whether each
// stop leaves two adjacent 1s (a dirty stop), and where the next round's block holding cell F starts (F-2, F-1 or F).
// gcc -O2 -o visps c/visps.c -lpthread; ./visps MACHINE TOPVISITS - THREADS REPORTEVERY
// Pipelined visit-law simulator (F02 visit law, lean/Visit.lean). Same model as vis.c in
// holdouts/1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---/c/: rules learned from the machine's table by simulating a visit,
// counts of visits kept as 2^e - c (or exact), a block of cells receiving n visits handled in one step.
//
// Three changes, each checked against vis.c (identical tape dumps at 5,000 and 20,000 rounds of
// 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---) and against busycoq PR59 (1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---
// halts in top visit 322,423, which is round 161,211):
//
// 1. Several rounds at once. A round is one top-level visit; its cascade (batch) only moves right: the outermost
//    loop of batch() works at a position p that never decreases, and everything it does (nested visits, raw
//    simulation, reading the window) touches cells >= p. So round r+1 may work on every cell left of round r's
//    outermost position (its "base") without changing anything round r will see, and round r never comes back to
//    cells round r+1 has touched. Every round waits until all earlier rounds still running have their base past the
//    cells it is about to touch (MARGIN cells to spare). The tape is the tape of the sequential program, cell for
//    cell. A halt found by round r is reported only after every earlier round has finished, the smallest round wins.
// 2. The prefix (10)^a in one jump: j blocks 1010 turn n visits into n*2^j visits of what follows, the blocks written
//    back unchanged (lean/VisitPow.lean, visN_rep1010). Their cells never change again, so they are checked once.
// 3. Preperiod and cycle. vis.c compresses a block whose rules repeat from the first one; here a block may first go
//    through T other rules (e.g. 010 -> 110 -> 000 -> 100 -> 000 ...). Accepted only when every rule with nested
//    visits has the same width W and no rule reads past W, so all nested visits go to p+W and can be added up.
//    The rule 1011 is never compressed, so every use of it is counted and printed (E1011 lines).
//
// gcc -O2 -o visp c/visp.c -lpthread
// usage: visp MACHINE TOPVISITS [DUMPFILE|-] [THREADS] [REPORTEVERY]     (rounds = top visits for A1 = 1LD)
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <pthread.h>
#include <setjmp.h>
#include <stdatomic.h>
#include <emmintrin.h>
#include <sched.h>
#include <limits.h>
typedef unsigned __int128 u128;
typedef __int128 i128;
typedef struct { int big; int64_t e; i128 c; } cnt;   // big: 2^e - c (c may be negative); else c >= 0
static int tmw[6][2], tmd[6][2], tms[6][2];
static long TSZ=1L<<31; static long ORG;
static uint8_t *tape0, *tape;
static int SIN=2, SOUT=0;
#define MAXW 12
#define MARGIN (2*MAXW+8)
#define GAP 2048
#define PUBSTEP 128
typedef struct { _Atomic uint8_t valid; uint8_t k; uint16_t out; } rule;
static rule *rules[MAXW+1];
static atomic_int nrules=0;
static pthread_mutex_t mu=PTHREAD_MUTEX_INITIALIZER;
static long maxround=0, reportevery=1L<<16; static int NT=3;
static time_t t0;
static atomic_long halted_round; // LONG_MAX if none
static long halt_pos; static int halt_st, halt_c; static char halt_win[128];
static atomic_long n1011; static FILE *LOG;
static long *finalpos; static signed char *nextoff; static unsigned char *dirtystop; static long evr[100000], evp[100000]; static int nev=0;
// ---- workers ----
#define MAXS 12
typedef struct { int stamp; uint8_t ok, W, T, L, M, KT; uint8_t k[MAXS]; uint16_t fin[MAXS]; } cyc;
typedef struct {
  _Atomic long round;      // round of the wave in this slot
  _Atomic long base;       // outermost position of the running wave (LONG_MAX when idle)
  _Atomic int  busy;
  long start; cnt count;   // job
  long lim, pub;           // cached limit (for the running wave), last published base
  long hi;                 // highest cell written
  long fmax;
  long nsingle, nbsteps, nraw, rawsteps, waits;
  int depth, maxdepth;
  cyc cycs[1<<MAXW];
  jmp_buf jb;
  long lg[4096]; int nlg;
  pthread_t th; int id;
} worker;
static worker *W_;
static void DIEF(const char *m, long a){ fprintf(stderr,"DIE: %s %ld\n",m,a); exit(3); }
// the smallest base of all waves of earlier rounds that are still running
static long minbase_before(long r){
  long m=LONG_MAX;
  for(int i=0;i<NT;i++){ worker *w=&W_[i];
    long b=atomic_load_explicit(&w->base,memory_order_acquire);
    long rr=atomic_load_explicit(&w->round,memory_order_acquire);
    if(rr<r && b<m) m=b; }
  return m; }
static inline void need(worker *w, long q){   // wave may touch cells < q
  if(q<w->lim) return;
  long r=atomic_load_explicit(&w->round,memory_order_relaxed);
  int waited=0;
  for(;;){ long m=minbase_before(r); if(m>q+(waited?GAP:0)){ w->lim=m; return; }
    w->waits++; waited=1;
    if(atomic_load_explicit(&halted_round,memory_order_relaxed)<r) longjmp(w->jb,2);
    sched_yield(); } }
static cnt one(void){ cnt r={0,0,1}; return r; }
static inline cnt norm(cnt n){
  if(n.big){
    if(n.e<=100){ i128 v=((i128)1<<n.e); if(n.c>v) DIEF("norm neg",0); n.big=0; n.c=v-n.c; n.e=0; }
    else if(n.c>((i128)1<<100) || n.c< -((i128)1<<100)) DIEF("big c overflow",0);
  } else if(n.c>>110){ int e=0; while(e<126 && ((i128)1<<e)<n.c) e++; i128 c=((i128)1<<e)-n.c;
    if(c>>90) DIEF("exact overflow",0); n.big=1; n.e=e; n.c=c; }
  return n; }
static inline int win(long p){ __m128i v=_mm_loadu_si128((const __m128i*)(tape+p)); return _mm_movemask_epi8(_mm_slli_epi16(v,7)) & ((1<<MAXW)-1); }
static inline void setwin(worker *w,long p,int n,int b){ for(int i=0;i<n;i++) tape[p+i]=(b>>i)&1; if(p+n>w->hi) w->hi=p+n; }
static void batch(worker *w,long p, cnt n, int outer);
static void halt(worker *w,int st,int c,long pos){
  long r=atomic_load(&w->round);
  pthread_mutex_lock(&mu);
  if(r<atomic_load(&halted_round)){ atomic_store(&halted_round,r); halt_pos=pos; halt_st=st; halt_c=c;
    int k=0; for(long i=pos-40;i<=pos+40;i++){ if(i==pos) halt_win[k++]='['; halt_win[k++]='0'+tape[i]; if(i==pos) halt_win[k++]=']'; } halt_win[k]=0; }
  pthread_mutex_unlock(&mu);
  longjmp(w->jb,1); }
static void raw(worker *w,long p){
  long pos=p, tmax=p, q=-1; int st=SIN, nsub=0, reg=1; long n=0;
  int init=0, seen=0;
  w->nraw++;
  for(;;){
    need(w,pos+MARGIN);
    if(st==SIN && tape[pos-1]==0 && pos>tmax){
      if(nsub==0) q=pos; else if(q!=pos) reg=0;
      nsub++; batch(w,pos, one(),0); pos-=2; st=SOUT;
      if(pos<=p-2) DIEF("sub returned outside",p);
      continue;
    }
    int c=tape[pos];
    if(pos>tmax) tmax=pos;
    { long o=pos-p; if(o>=0 && o<MAXW && !((seen>>o)&1)){ seen|=1<<o; init|=c<<o; } }
    if(tmw[st][c]<0){ halt(w,st,c,pos); }
    tape[pos]=tmw[st][c]; if(pos>=w->hi) w->hi=pos+1;
    pos+=tmd[st][c]; st=tms[st][c]; n++; w->rawsteps++;
    if(n>100000000) DIEF("raw visit too long at",p);
    if(pos==p-2){ if(st!=SOUT||tape[p-1]!=0) DIEF("bad return at",p); break; }
  }
  long wd;
  if(nsub){ if(!reg||tmax>=q) return; wd=q-p; } else wd=tmax+1-p;
  if(wd>MAXW || wd<1) return;
  if((seen&((1<<wd)-1))!=(1<<wd)-1) return;
  pthread_mutex_lock(&mu);
  rule *r=&rules[wd][init&((1<<wd)-1)];
  if(!atomic_load(&r->valid)){ r->k=nsub; int o=0; for(int i=0;i<wd;i++) o|=tape[p+i]<<i; r->out=o;
    atomic_store(&r->valid,1); atomic_fetch_add(&nrules,1);
    if(wd==4 && (init&15)==13){ evr[nev]=atomic_load(&w->round); evp[nev]=p; nev++; }
    fprintf(stderr,"rule w=%ld ",wd); for(int i=0;i<wd;i++) fputc('0'+((init>>i)&1),stderr); fprintf(stderr," -> ");
    for(int i=0;i<wd;i++) fputc('0'+tape[p+i],stderr); fprintf(stderr," subs=%d (round %ld)\n",nsub,atomic_load(&w->round)); }
  pthread_mutex_unlock(&mu);
}
static inline int match(int buf,int *wd){ for(int i=1;i<=MAXW;i++){ rule *r=&rules[i][buf&((1<<i)-1)]; if(atomic_load_explicit(&r->valid,memory_order_acquire)){ *wd=i; return 1; } } return 0; }
// The rules met by visits to the window at p, one after the other: a preperiod of T rules, then a cycle of L rules.
// Accepted only when every rule with nested visits has the same width W and no rule reads past W (so the nested
// visits all go to p+W, and visits to p+W may be added up), and the rule 1011 does not occur (it is counted singly).
static cyc *findcycle(worker *w,long p){
  int b0=win(p); cyc *cy=&w->cycs[b0]; int nr=atomic_load_explicit(&nrules,memory_order_relaxed);
  if(cy->stamp==nr+1) return cy->ok?cy:NULL;
  cy->stamp=nr+1; cy->ok=0;
  int bufs[MAXS+1], ks[MAXS]; int buf=b0, sw=0, Wm=0; bufs[0]=b0;
  for(int i=1;i<=MAXS;i++){
    int wd; if(!match(buf,&wd)) return NULL;
    if(wd==4 && (buf&15)==13) return NULL;
    rule *r=&rules[wd][buf&((1<<wd)-1)];
    buf=(buf&~((1<<wd)-1))|r->out; bufs[i]=buf; ks[i-1]=r->k;
    if(r->k){ if(sw&&sw!=wd) return NULL; sw=wd; }
    if(wd>Wm) Wm=wd;
    if(sw && Wm>sw) return NULL;
    int W=sw?sw:Wm, m=(1<<W)-1;
    for(int j=0;j<i;j++) if((bufs[j]&m)==(buf&m)){
      int T=j, L=i-j, M=0, KT=0; for(int t=0;t<T;t++) KT+=ks[t]; for(int t=T;t<i;t++) M+=ks[t];
      cy->ok=1; cy->W=W; cy->T=T; cy->L=L; cy->M=M; cy->KT=KT;
      for(int t=0;t<i;t++){ cy->k[t]=ks[t]; cy->fin[t]=bufs[t+1]&m; }
      return cy; }
  }
  return NULL;
}
static int ilog2x(int M){ int m=0; while((1<<m)<M) m++; if((1<<m)!=M) return -1; return m; }
static void batch(worker *w,long p, cnt n, int outer){
  if(++w->depth>w->maxdepth) w->maxdepth=w->depth;
  for(;;){
    if(!n.big && n.c==0) break;
    if(outer && p-w->pub>=PUBSTEP){ w->pub=p; atomic_store_explicit(&w->base,p,memory_order_release); }
    need(w,p+MARGIN);
    if(p+4*MAXW>=TSZ-ORG) DIEF("tape overflow",p);
    w->nbsteps++;
    { long r=atomic_load_explicit(&w->round,memory_order_relaxed); if(r>1){ long F=finalpos[r-1]; if(F && p>=F-48 && !n.big && w->nlg<4094){ w->lg[w->nlg++]=p-F; w->lg[w->nlg++]=(long)n.c; } } }
    if(p>w->fmax) w->fmax=p;
    { long r=atomic_load_explicit(&w->round,memory_order_relaxed); if(r>1){ long F=finalpos[r-1]; if(F && p>=F-4 && p<=F && (nextoff[r]==127 || p-F>nextoff[r])) nextoff[r]=(signed char)(p-F); } }
    cyc *cy=findcycle(w,p);
    if(cy){
      int T=cy->T, L=cy->L, M=cy->M; int fin; cnt tot; int ok=1;
      if(!n.big){
        if(n.c<=T){ int sub=0; for(int i=0;i<(int)n.c;i++) sub+=cy->k[i]; tot.big=0; tot.e=0; tot.c=sub; fin=cy->fin[n.c-1]; }
        else { i128 m=n.c-T, full=m/L; int rem=(int)(m%L), part=0; for(int i=0;i<rem;i++) part+=cy->k[T+i];
          tot.big=0; tot.e=0; tot.c=cy->KT+full*M+part; fin=cy->fin[(rem?T+rem:T+L)-1]; }
      } else {
        int l=(L==1?0:L==2?1:L==4?2:-1), mm=(M==0?0:ilog2x(M));
        if(l<0 || mm<0) ok=0;
        else {
          i128 c=n.c+T, cc; int rem;   // m = n - T = 2^e - c
          if(L==1){ rem=0; cc=c; } else if(L==2){ rem=(int)(c&1); cc=(c+1)>>1; } else { rem=(int)((4-(int)(c&3))&3); cc=(c+3)>>2; }
          int part=0; for(int i=0;i<rem;i++) part+=cy->k[T+i];
          if(M==0){ tot.big=0; tot.e=0; tot.c=cy->KT+part; }
          else { tot.big=1; tot.e=n.e-l+mm; tot.c=(cc<<mm)-cy->KT-part; }
          fin=cy->fin[(rem?T+rem:T+L)-1];
        }
      }
      if(ok){ setwin(w,p,cy->W,fin); p+=cy->W; n=norm(tot); continue; }
    }
    w->nsingle++;
    int wd, b=win(p);
    if(match(b,&wd)){ rule *r=&rules[wd][b&((1<<wd)-1)];
      if(wd==4 && (b&15)==13){ long k=atomic_fetch_add(&n1011,1)+1;
        if(k<=100000){ fprintf(stderr,"E1011 round %ld pos %ld\n",atomic_load(&w->round),p); pthread_mutex_lock(&mu); evr[nev]=atomic_load(&w->round); evp[nev]=p; nev++; pthread_mutex_unlock(&mu);} }
      setwin(w,p,wd,r->out); if(r->k){ cnt k={0,0,r->k}; batch(w,p+wd,k,0);} }
    else raw(w,p);
    if(n.big) n.c+=1; else n.c-=1;
    n=norm(n);
  }
  w->depth--;
}
static void *wloop(void *arg){
  worker *w=arg;
  for(;;){
    while(!atomic_load_explicit(&w->busy,memory_order_acquire)) sched_yield();
    if(atomic_load(&w->round)<0) return NULL;
    w->lim=0; w->depth=0; w->pub=w->start; w->fmax=w->start;
    w->nlg=0;
    if(!setjmp(w->jb)) batch(w,w->start,w->count,1);
    { long r=atomic_load(&w->round), f=w->fmax; int dz=0; for(long i=f;i<f+4;i++) if(tape[i]&&tape[i+1]) dz=1; dirtystop[r]=dz; finalpos[r]=f;
      pthread_mutex_lock(&mu); fprintf(LOG,"R %ld F %ld d %d W ",r,f,dz); for(long i=f-48;i<f+48;i++) fputc('0'+tape[i],LOG); fprintf(LOG," V"); for(int i=0;i<w->nlg;i+=2) fprintf(LOG," %ld:%ld",w->lg[i],w->lg[i+1]); fputc('\n',LOG); pthread_mutex_unlock(&mu); }
    atomic_store_explicit(&w->base,LONG_MAX,memory_order_release);
    atomic_store_explicit(&w->busy,0,memory_order_release);
  }
}
// ---- main thread: the machine near the left end, one wave per top-level visit ----
static long lo=0; static long Vlo=LONG_MIN, Bv=LONG_MIN; static long topvis=0;
static void wait_clear(long q){ for(;;){ long m=minbase_before(LONG_MAX); if(m>q) return; sched_yield(); } }
static void report(const char *tag){
  long ns=0,nb=0,nr=0,rs=0,wt=0,hi=0; int md=0;
  for(int i=0;i<NT;i++){ worker *w=&W_[i]; ns+=w->nsingle; nb+=w->nbsteps; nr+=w->nraw; rs+=w->rawsteps; wt+=w->waits; if(w->hi>hi) hi=w->hi; if(w->maxdepth>md) md=w->maxdepth; }
  fprintf(stderr,"%s topvis %ld lo %ld hi %ld singles %ld bsteps %ld raws %ld rawsteps %ld waits %ld rules %d maxdepth %d n1011 %ld t %lds\n",
    tag,topvis,lo,hi,ns,nb,nr,rs,wt,atomic_load(&nrules),md,atomic_load(&n1011),(long)(time(0)-t0));
}
static void dispatch(long pos){
  long r=topvis;
  // the prefix: cells [Vlo,Bv) are pairs 10 that never change again; check the new cells left of Vlo
  if(Vlo!=LONG_MIN && pos<Vlo){ int ok=((Vlo-pos)&1)==0; for(long i=pos;ok&&i<Vlo;i+=2) if(tape[i]!=1||tape[i+1]!=0) ok=0;
    if(ok) Vlo=pos; else Vlo=Bv=LONG_MIN; }
  if(Vlo!=LONG_MIN && (pos<Vlo || ((pos-Vlo)&1))) Vlo=Bv=LONG_MIN;
  long x=pos;
  if(Vlo!=LONG_MIN) x=pos+4*((Bv-pos)/4);
  for(;;){ wait_clear(x+MARGIN); if(tape[x]==1&&tape[x+1]==0&&tape[x+2]==1&&tape[x+3]==0) x+=4; else break; }
  if(Vlo==LONG_MIN) Vlo=pos;
  Bv=x;
  long j=(x-pos)/4;
  cnt c; if(j<100){ c.big=0; c.e=0; c.c=(u128)1<<j; } else { c.big=1; c.e=j; c.c=0; }
  // find a free worker (waves of round r-NT and earlier are done, or wait)
  worker *w=&W_[r%NT];
  while(atomic_load_explicit(&w->busy,memory_order_acquire)) sched_yield();
  w->start=x; w->count=c;
  atomic_store_explicit(&w->base,x,memory_order_release);
  atomic_store_explicit(&w->round,r,memory_order_release);
  atomic_store_explicit(&w->busy,1,memory_order_release);
}
static void dump(const char *fn,long pos){ long hi=0; for(int i=0;i<NT;i++) if(W_[i].hi>hi) hi=W_[i].hi;
  long a=lo,b=hi+64; while(a<b&&!tape[a])a++; while(b>a&&!tape[b-1])b--; FILE *f=fopen(fn,"w"); fprintf(f,"%ld %ld %ld\n",a,b,pos); for(long i=a;i<b;i++) fputc('0'+tape[i],f); fputc('\n',f); fclose(f); }
static void finish(const char *dumpfile,long pos){
  for(int i=0;i<NT;i++) while(atomic_load(&W_[i].busy)) sched_yield();
  long hr=atomic_load(&halted_round);
  if(hr!=LONG_MAX){ printf("HALT state %c reading %d at pos %ld during top visit %ld\nwindow: %s\n",'A'+halt_st,halt_c,halt_pos,hr,halt_win); report("halt"); }
  else report("end");
  for(int i=0;i<nev;i++){ long r=evr[i]; fprintf(stderr,"EV round %ld pos %ld final[r-1] %ld final[r] %ld p-(final[r-1]-2) %ld\n",r,evp[i],finalpos[r-1],finalpos[r],evp[i]-(finalpos[r-1]-2)); }
  { long cnt[3][16]={{0}}; long nd=0; for(long r=2;r<maxround;r++){ int o=nextoff[r]; int k=(o==127)?15:(o+4); if(k<0||k>15)k=15; cnt[dirtystop[r-1]?1:0][k]++; if(dirtystop[r-1]){ nd++; if(nd<=40) fprintf(stderr,"DIRTY stop round %ld at %ld, next round's block holding F starts at F%+d\n",r-1,finalpos[r-1],o==127?99:o);} }
    fprintf(stderr,"dirty stops %ld\n",nd);
    for(int d=0;d<2;d++){ fprintf(stderr,"%s stop: next round's block holding cell F starts at:",d?"dirty":"clean"); for(int k=0;k<16;k++) if(cnt[d][k]) fprintf(stderr," %s%d:%ld",k==15?"none":"F",k==15?0:k-4,cnt[d][k]); fprintf(stderr,"\n"); } }
  { long mx=0; for(long r=1;r<maxround;r++){ long d=finalpos[r]-finalpos[r-1]; if(r>1&&(d>mx||-d>mx)) mx=d<0?-d:d; } fprintf(stderr,"max |final[r]-final[r-1]| %ld\n",mx); }
  if(dumpfile) dump(dumpfile,pos);
  fflush(LOG); exit(0);
}
int main(int argc,char **argv){
  const char *s=argv[1]; if(argc>2) maxround=atol(argv[2]); const char *dumpfile=(argc>3&&strcmp(argv[3],"-"))?argv[3]:NULL;
  if(argc>4) NT=atoi(argv[4]); if(argc>5) reportevery=atol(argv[5]);
  if(getenv("TSZLOG")) TSZ=1L<<atoi(getenv("TSZLOG"));
  ORG=TSZ/4;
  for(int q=0;q<6;q++) for(int c=0;c<2;c++){ const char *t=s+q*7+c*3;
    if(t[0]=='-'){ tmw[q][c]=-1; } else { tmw[q][c]=t[0]-'0'; tmd[q][c]=t[1]=='R'?1:-1; tms[q][c]=t[2]-'A'; } }
  finalpos=calloc(maxround+3,sizeof(long)); nextoff=malloc(maxround+3); memset(nextoff,127,maxround+3); dirtystop=calloc(maxround+3,1);
  tape0=calloc(TSZ,1); tape=tape0+ORG;
  for(int i=1;i<=MAXW;i++) rules[i]=calloc(1<<i,sizeof(rule));
  atomic_store(&halted_round,LONG_MAX);
  W_=calloc(NT,sizeof(worker));
  for(int i=0;i<NT;i++){ W_[i].id=i; atomic_store(&W_[i].base,LONG_MAX); atomic_store(&W_[i].round,LONG_MAX); pthread_create(&W_[i].th,NULL,wloop,&W_[i]); }
  t0=time(0); LOG=fopen(getenv("VLOG")?getenv("VLOG"):"v.log","w");
  // top-level raw simulation (vis.c raw(0,1)), every top-level visit becomes a wave
  long pos=0; int st=0;
  for(;;){
    if(atomic_load_explicit(&halted_round,memory_order_relaxed)!=LONG_MAX) finish(dumpfile,pos);
    wait_clear(pos+MARGIN);
    if(st==SIN && tape[pos-1]==0){
      topvis++;
      if(maxround && topvis>maxround) finish(dumpfile,pos);
      if((topvis%reportevery)==0) report("run");
      dispatch(pos); pos-=2; st=SOUT; continue;
    }
    int c=tape[pos];
    if(tmw[st][c]<0){ printf("HALT at top level state %c pos %ld topvis %ld\n",'A'+st,pos,topvis); finish(dumpfile,pos); }
    if(Vlo!=LONG_MIN && pos>=Vlo && pos<Bv) Vlo=Bv=LONG_MIN;
    tape[pos]=tmw[st][c]; if(pos<lo) lo=pos;
    pos+=tmd[st][c]; st=tms[st][c];
    if(pos< -ORG+64) DIEF("left overflow",pos);
  }
}
