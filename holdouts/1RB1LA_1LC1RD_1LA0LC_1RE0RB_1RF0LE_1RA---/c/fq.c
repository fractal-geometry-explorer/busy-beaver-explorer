/* Exact fast iteration of the round map F of busycoq pull request 40 (SOC25_Iter.v, F_spec),
   the map that 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0LE_1RA--- (from (L, X) = (8, 145)) and
   1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF1RC_1RA--- (from (1, 3)) are proved equivalent to.
   Reference implementation: ../py/F25.py (a transcription of F_spec).  check.sh compares the two.

   X is kept as a bit queue.  For X odd, let p be the lowest odd position holding a 1 bit of X
   (the 1 bit that closes the first even gap of div2 X).  Then a round is

       X' = 2^T + (X >> p) - V        (or 2^T - V when X has no such bit: the run-out case)

   with V a small correction (about 3.5 p bits) built from the gaps F read, and T = L'.  So each
   round drops p bits at the bottom, rewrites a short zone above them, and sets one new top bit.
   Cost per round is proportional to the bits read and rewritten, not to the length of X.

   Counted along the way (odd rounds from round 7 on):
     - marker bits: 1 bits of div2 X at even positions (= 1 bits of X at odd positions);
       F_marker (coq/SOC25_Marker.v) says a halt needs a round with none;
     - the queue law: p = 2k+1, L' = L + 5k + 3, and the new top bit sits 7k + 4 above the old top
       bit (which is X's top bit shifted down by p and otherwise untouched); checked every round;
     - pushes with an odd gap (k odd): the two top bits then have different parity, a marker;
     - the longest run of rounds with k even, the widest bottom rewrite, the smallest marker/round.

   usage: fq L X ROUNDS [EVERY] [CHECK]
     EVERY: progress line on stderr every EVERY rounds (0: none)
     CHECK=1: print "t L X mod (2^61-1)" every round, for comparison with py/F25.py */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t u64;
/* ---------- small bigint (nonnegative) ---------- */
typedef struct { u64 *d; int n, cap; } bn;
static void bn_fit(bn *a, int n){ if(n>a->cap){ int c=a->cap?a->cap:4; while(c<n)c*=2; a->d=realloc(a->d,c*8); memset(a->d+a->cap,0,(c-a->cap)*8); a->cap=c;} if(n>a->n){ a->n=n; } }
static void bn_norm(bn *a){ while(a->n>0 && a->d[a->n-1]==0) a->n--; }
static void bn_set_u(bn *a, u64 v){ if(a->cap) memset(a->d,0,a->cap*8); a->n=0; bn_fit(a,1); a->d[0]=v; a->n=1; bn_norm(a); }
static void bn_add_pow2(bn *a, long j){ int w=j/64; bn_fit(a,w+2); u64 c=1ULL<<(j%64); for(int i=w;c;i++){ if(i>=a->n) bn_fit(a,i+1); u64 s=a->d[i]+c; c=(s<c); a->d[i]=s; } bn_norm(a);}
static void bn_sub_pow2(bn *a, long j){ int w=j/64; u64 b=1ULL<<(j%64); for(int i=w;b;i++){ if(i>=a->n){fprintf(stderr,"bn underflow\n");exit(2);} u64 s=a->d[i]-b; b=(a->d[i]<b); a->d[i]=s; } bn_norm(a);}
static void bn_shl(bn *a, long c){ if(a->n==0) return; int w=c/64, r=c%64; int n=a->n; bn_fit(a,n+w+1); a->d[n+w]=0;
  for(int i=n-1;i>=0;i--){ u64 v=a->d[i]; a->d[i+w+1] |= r? (v>>(64-r)) : 0; a->d[i+w] = v<<r; }
  for(int i=0;i<w;i++) a->d[i]=0; /* careful: loop above writes d[i+w] after reading d[i]; going down is safe */
  a->n=n+w+1; bn_norm(a);}
static long bn_bits(bn *a){ if(a->n==0) return 0; return 64*(long)(a->n-1) + 64-__builtin_clzll(a->d[a->n-1]); }
static int bn_bit(bn *a, long j){ int w=j/64; if(w>=a->n) return 0; return (a->d[w]>>(j%64))&1; }

/* ---------- bit queue for X ---------- */
static u64 *Q; static long QW;        /* words */
static long lo, hi;                   /* bit index of X's bit 0; index one past highest set bit (hi==lo: X==0) */
static long cnt[2]; static long lastext=0, maxext=0, front=0, maxfront=0; static long lawfail=0; static long evrun=0,maxevrun=0,maxevrun_t=0; static double minratio=1e300; static long minratio_t=-1;                   /* ones at absolute even / odd index */
static long ones;
static inline int qget(long i){ return (Q[i>>6]>>(i&63))&1; }
static inline void qset(long i){ Q[i>>6] |= 1ULL<<(i&63); cnt[i&1]++; ones++; }
static inline void qclr(long i){ Q[i>>6] &= ~(1ULL<<(i&63)); cnt[i&1]--; ones--; }
static void qensure(long top){ /* make index top valid; compact if needed */
  if((top>>6)+2 < QW) return;
  long w0 = (lo>>6);
  if(w0 > QW/2){ /* compact: shift by whole words (keeps parity since 64 even) */
    memmove(Q, Q+w0, (QW-w0)*8); memset(Q+QW-w0,0,w0*8); lo-=w0*64; hi-=w0*64; top-=w0*64;
    if((top>>6)+2 < QW) return; }
  long nw=QW*2; while((top>>6)+2>=nw) nw*=2; Q=realloc(Q,nw*8); memset(Q+QW,0,(nw-QW)*8); QW=nw; }
/* next set bit at index >= i, or -1 if none below hi */
static long qnext(long i){ if(i>=hi) return -1; long w=i>>6; u64 v=Q[w] & (~0ULL<<(i&63));
  while(!v){ w++; if(w*64>=hi) return -1; v=Q[w]; } long r=w*64+__builtin_ctzll(v); return r<hi?r:-1; }
static long qprev(long i){ /* highest set bit at index <= i, >= lo; -1 if none */
  if(i<lo) return -1; long w=i>>6; u64 v=Q[w] & ((i&63)==63? ~0ULL : ((1ULL<<((i&63)+1))-1));
  while(!v){ if(w*64<=lo) return -1; w--; v=Q[w]; } long r=w*64+63-__builtin_clzll(v); return r>=lo?r:-1; }
static void fixhi(void){ /* recompute hi downward */ while(hi>lo && !qget(hi-1)) hi--; }

/* X := 2^T + (X >> p) - V ; restgone: X had no bits at/after p (rest = 0) */
static void apply(long p, long T, bn *V){
  /* drop bits below lo+p */
  long i=qnext(lo); while(i>=0 && i<lo+p){ qclr(i); i=qnext(i+1); }
  lo += p; if(hi<lo) hi=lo;
  qensure(lo+T+2);
  /* add 2^T */
  long j=lo+T; while(qget(j)){ qclr(j); j++; } qset(j); if(j+1>hi) hi=j+1;
  /* subtract V */
  lastext=0; long nb=bn_bits(V);
  for(long b=0;b<nb;b++) if(bn_bit(V,b)){
    long k=lo+b; while(!qget(k)){ qset(k); k++; if(k>=hi){fprintf(stderr,"negative X\n");exit(3);} } qclr(k);
    if(k-lo+1>lastext) lastext=k-lo+1;
  }
  fixhi();
}
static long v2from(long start, long *pos){ /* zeros from start to next set bit; -1 if none */
  long n=qnext(start); if(n<0) return -1; *pos=n; return n-start; }

static const u64 MP=(1ULL<<61)-1;
static u64 xmod(void){ unsigned __int128 r=0; for(long i=hi-1;i>=lo;i--){ r=(r*2+qget(i))%MP; } return (u64)r; }

int main(int argc,char**argv){
  long L=atol(argv[1]); unsigned long long X0=strtoull(argv[2],0,10); long N=atol(argv[3]);
  long EVERY = argc>4?atol(argv[4]):100000; int CHECK = argc>5?atoi(argv[5]):0;
  QW=1<<16; Q=calloc(QW,8); lo=64; hi=lo; cnt[0]=cnt[1]=0; ones=0;
  for(int b=0;b<64;b++) if((X0>>b)&1){ qset(lo+b); hi=lo+b+1; }
  bn W={0}, V={0};
  long minmark=-1, minmark_t=-1; long nodd=0, neven=0;
  long hist[64]={0};
  long lawok=0, oddpush=0, maxp=0; static long khist[64]; long decmin[20]; for(int i=0;i<20;i++) decmin[i]=-1;
  for(long t=0;t<N;t++){
    int Xodd = (hi>lo) && qget(lo);
    if(t>=7 && Xodd){ long mk = cnt[(lo+1)&1]; if(minmark<0||mk<minmark){minmark=mk;minmark_t=t;} if(mk<64) hist[mk]++; { int dd=0; long tt=t; while(tt>=10){tt/=10;dd++;} if(decmin[dd]<0||mk<decmin[dd]) decmin[dd]=mk; } if(t>=100 && (double)mk/t<minratio){minratio=(double)mk/t; minratio_t=t;} }
    if(Xodd) nodd++; else neven++;
    if(CHECK){ printf("%ld %ld %llu\n",t,L,(unsigned long long)xmod()); }
    if(EVERY && t%EVERY==0){ fprintf(stderr,"t=%ld L=%ld ones=%ld mark=%ld minmark=%ld@%ld odd=%ld even=%ld\n",t,L,ones,Xodd?cnt[(lo+1)&1]:-1,minmark,minmark_t,nodd,neven); }
    long Lnew;
    /* special case X == 2^L */
    if(ones==1 && hi-1==lo+L){
      long l=L-1, a=l/2; long T;
      if(l%2==0){ T=l+2+5*a+2; Lnew=l+3+5*a+2; /* X'=2^T + 2^(5a+2) */
        long i=qnext(lo); qclr(i); hi=lo; qensure(lo+T+2); qset(lo+T); qset(lo+5*a+2); hi=lo+T+1; }
      else { T=l+2+5*a+4; Lnew=l+3+5*a+4; long i=qnext(lo); qclr(i); hi=lo; qensure(lo+T+2); qset(lo+T); qset(lo+5*a+4); qset(lo); hi=lo+T+1; }
      L=Lnew; continue;
    }
    long pos; long h=v2from(lo,&pos); if(h<0){fprintf(stderr,"X=0\n");return 4;}
    long p=pos-lo; /* position of lowest 1 of X */
    long a=h/2; long E=L;
    bn_set_u(&W,0); bn_add_pow2(&W,h+1); bn_sub_pow2(&W,0);       /* W = 2^(h+1)-1 */
    long np; long nexti = v2from(pos+1,&np);                   /* m = X>>(h+1); m==0 iff nexti<0 */
    if(h%2==1){
      if(nexti<0){ /* X' = 2^(E+1+5a+3) - (2W-1)2^(5a+3) */
        bn_shl(&W,1); bn_sub_pow2(&W,0); bn_shl(&W,5*a+3);
        Lnew=L+4+5*a; long T=E+1+5*a+3; /* rest gone */
        long i=qnext(lo); while(i>=0){ qclr(i); i=qnext(i+1);} hi=lo;
        apply(0,T,&W); L=Lnew; continue; }
      printf("HALT in round %ld L=%ld\n",t,L); return 0;
    }
    /* L1 = L+1+5a; K = (2k+1)2^(5a) - 1 */
    bn_shl(&W,1); bn_sub_pow2(&W,0); bn_shl(&W,5*a); bn_add_pow2(&W,0); E=L+1+5*a; long L1=E;
    if(nexti<0){ /* X' = 2^E - (W-2) */
      bn_sub_pow2(&W,1); long i=qnext(lo); while(i>=0){ qclr(i); i=qnext(i+1);} hi=lo;
      apply(0,E,&W); L=L1; continue; }
    long ig=nexti; long pp=np; /* gap i and position of its closing 1 */
    if(ig>0){ bn_add_pow2(&W,ig+1); bn_sub_pow2(&W,1); }         /* W += 2^(i+1)-2 */
    for(;;){
      long aa=ig/2;
      if(ig%2==0){ /* X' = 2^(E+5aa+2) - (2W-1)2^(5aa+1) + (X>>pp) */
        bn_shl(&W,1); bn_sub_pow2(&W,0); bn_shl(&W,5*aa+1);
        long T=E+5*aa+2; Lnew=L1+5*aa+2;
        long oldtop=hi-1-lo, pr=pp-lo;
        apply(pp-lo,T,&W);
        if(t>=10){ if(lastext>maxext) maxext=lastext; front = front-pr>lastext? front-pr : lastext; if(front>maxfront) maxfront=front; }
        { long nt=hi-1-lo, sec=qprev(hi-2)-lo; long k=(pr-1)/2;
          if(pr%2!=1 || nt!=T || sec!=oldtop-pr || T-sec!=7*k+4 || Lnew-L!=5*k+3 || nt!=Lnew){ lawfail++; if(lawfail<20) fprintf(stderr,"law fails t=%ld p=%ld T=%ld sec=%ld oldtop=%ld L=%ld L'=%ld\n",t,pr,T,sec,oldtop,L,Lnew);} 
          else { lawok++; if(k<64) khist[k]++; else khist[63]++; if(k&1){ oddpush++; evrun=0; } else { evrun++; if(evrun>maxevrun){maxevrun=evrun; maxevrun_t=t;} } if(pr>maxp) maxp=pr; } }
        break; }
      bn_shl(&W,1); bn_sub_pow2(&W,0); bn_shl(&W,5*aa+4); bn_add_pow2(&W,0); E=E+5*aa+5; L1=L1+5*aa+5;
      long np2; long i2=v2from(pp+1,&np2);
      if(i2<0){ /* X' = 2^E - (W-1) */
        bn_sub_pow2(&W,0); long i=qnext(lo); while(i>=0){ qclr(i); i=qnext(i+1);} hi=lo;
        apply(0,E,&W); Lnew=L1; break; }
      bn_add_pow2(&W,i2+1); bn_sub_pow2(&W,0);                       /* W += 2^(i2+1)-1 */
      ig=i2; pp=np2;
    }
    L=Lnew;
  }
  printf("done %ld rounds L=%ld ones=%ld minmark=%ld@%ld odd=%ld even=%ld\n",N,L,ones,minmark,minmark_t,nodd,neven);
  printf("queue law (X odd, final even gap): holds %ld rounds, fails %ld; p=2k+1 max %ld; pushes with odd gap (k odd) %ld\n",lawok,lawfail,maxp,oddpush);
  printf("longest run of consecutive even pushes (k even): %ld rounds, ending at round %ld\n",maxevrun,maxevrun_t);
  printf("smallest marker/round ratio from round 100: %.6f at round %ld\n",minratio,minratio_t);
  printf("bottom rewrite (from round 10): widest %ld bits; rewritten zone never deeper than %ld bits\n",maxext,maxfront);
  printf("k distribution:"); for(int k=0;k<64;k++) if(khist[k]) printf(" %d:%ld",k,khist[k]); printf("\n");
  printf("fewest marker bits by decade of rounds [10^j,10^(j+1)), from round 7:"); for(int j=0;j<20;j++) if(decmin[j]>=0) printf(" j=%d:%ld",j,decmin[j]); printf("\n");
  printf("hist(marker count: odd rounds from 7):"); for(int k=0;k<64;k++) if(hist[k]) printf(" %d:%ld",k,hist[k]); printf("\n");
  return 0;
}
