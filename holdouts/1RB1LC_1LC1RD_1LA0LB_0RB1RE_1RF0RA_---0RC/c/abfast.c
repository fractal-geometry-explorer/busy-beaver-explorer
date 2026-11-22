/* abfast.c: the A(a,b) rules of 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC, up to 48 visits at a time.

   Same orbit as abrun.c (from A(2,9)), same "near" log (every visit with 1 <= b - a <= 8) and reset log, but no
   machine step count. Write s = a + b and d = b - a. Away from the resets the rules are
       grow  (d > 0):  d' = 2d - s + c,  s' = s + 3,  c = -5 if a is even, -3 if a is odd
       swap  (d <= 0): d' = 2d + s + 2,  s' = s + 4
   a doubling map on d/s in (-1, 1) (grow is "digit 1", swap "digit 0"). Each block of K visits (K a multiple of 4,
   the largest with 32 * 2^K <= s / 64, at most 48; 32 for s from 2^43 to 2^47):
     1. guess the K digits as the top bits of (d/s + 1)/2 (a double; a wrong guess is caught in step 3),
     2. apply the guessed digits formally (the two formulas, whatever the sign of d) with tables of 8 and 4
        digits (the constants c and the growth of s depend only on the digits and on a mod 2, s mod 2, and these
        follow from the digits: grow keeps a mod 2 and flips s mod 2, swap sets a mod 2 to s + 1 and keeps s mod 2),
        giving dK, sK exactly in 128-bit integers,
     3. accept only if  -sK + G <= dK <= sK - G  with G = 32 * 2^K, that is both aK and bK >= 16 * 2^K.
   If step 3 fails the block is redone one visit at a time with the full rules (resets, halt, near log).

   Why step 3 is enough: lean/Block.lean, block_ok. For any digits, if their formal run (drun) ends with both
   coordinates >= 16 * 2^K, the K visits are that run of op; block_far: none of them has 1 <= b - a <= 27, so no
   halt, reset or near visit is skipped. (One formal step at most doubles min(a, b) plus 4, so every formal step
   of an accepted block ends with both coordinates >= 28, and such a step is the step of op.)

   usage: abfast N [logevery [i0 a b]]   (resume from a logged prog line)
   Prints "near", "reset", "prog" lines like abrun.c, and at the end the counts of exact and fast blocks. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef __int128 i128;
typedef unsigned long long u64;
typedef long long i64;

/* table entry for 8 digits from low state st = (apar | spar<<1) */
typedef struct { i64 p, q; int ds, st; } Ent;
static Ent TB[4][256];
static i64 QT[4][256], QT4[4][16];   /* q of TB, the only part the inner loop looks up */

static void mktab(void){
  for(int st=0;st<4;st++) for(int by=0;by<256;by++){
    int ap=st&1, sp=(st>>1)&1; i64 p=0,q=0; int ds=0;
    for(int i=0;i<8;i++){
      int bit=(by>>(7-i))&1; int sg=bit?1:-1; int c,inc;
      if(bit){ c=ap?-3:-5; inc=3; /* a parity kept */ sp^=1; }
      else   { c=2; inc=4; ap=(sp+1)&1; /* s parity kept */ }
      p=2*p+sg; q=2*q+(c-(i64)sg*ds); ds+=inc;
    }
    TB[st][by]=(Ent){p,q,ds,ap|(sp<<1)}; QT[st][by]=q;
    if(by<16){ /* the 4-digit table: the same recursion over 4 digits */
      int ap4=st&1, sp4=(st>>1)&1; i64 q4=0; int ds4=0;
      for(int i2=0;i2<4;i2++){ int bit=(by>>(3-i2))&1; int sg=bit?1:-1; int c,inc;
        if(bit){ c=ap4?-3:-5; inc=3; sp4^=1; } else { c=2; inc=4; ap4=(sp4+1)&1; }
        q4=2*q4+(c-(i64)sg*ds4); ds4+=inc; }
      QT4[st][by]=q4; }
  }
}


/* low state (a mod 2 | (s mod 2) << 1) after the n digits pre (msb first) from state (ap0, sp0):
   s mod 2 flips at each grow; a mod 2 is kept by grow and set to (s + 1) mod 2 by swap. */
static inline int stafter(u64 pre, int n, int ap0, int sp0){
  int sp = sp0 ^ (__builtin_popcountll(pre)&1);
  u64 inv = (~pre) & ((n>=64)? ~0ULL : ((1ULL<<n)-1));
  int ap = ap0;
  if(inv){ int tz=__builtin_ctzll(inv); ap = 1 ^ sp0 ^ (__builtin_popcountll(pre>>(tz+1))&1); }
  return ap | (sp<<1);
}

/* Blocks of K visits (K = 8m + 4h, h = 0 or 1: m tables of 8 digits, then one of 4), while they are accepted and
   stay before 'lim'. Returns the number of blocks done. */
#define FASTRUN(K) \
static u64 fastrun##K(i64*pd, i64*ps, u64*pi, u64 lim){ \
  enum { M=(K)/8, HN=((K)%8)/4 }; \
  i64 d=*pd, s=*ps; u64 i=*pi, n=0; const double H=(double)(1ULL<<((K)-1)); double rH=H/(double)s; \
  const i128 G=((i128)32)<<(K); \
  while(i+(K)<=lim){ \
    double y=__builtin_fma((double)d,rH,H); \
    if(!(y>0 && y<2*H)) break; \
    u64 Q=(u64)y; int ap0=(int)(((s-d)>>1)&1), sp0=(int)(s&1); \
    i128 T=0; \
    for(int j=0;j<M;j++){ \
      u64 pre = j? Q>>((K)-8*j) : 0; int by=(int)((Q>>((K)-8-8*j))&255); \
      int st = j? stafter(pre,8*j,ap0,sp0) : (ap0|(sp0<<1)); \
      i64 Sj = s + 32*j - __builtin_popcountll(pre); \
      T += (i128)(Sj*(i64)(2*by-255) - QT[st][by]) << (8*(M-1-j)+4*HN); \
    } \
    if(HN){ u64 pre=Q>>4; int nb=(int)(Q&15); int st = M? stafter(pre,8*M,ap0,sp0) : (ap0|(sp0<<1)); \
      i64 Sj = s + 32*M - __builtin_popcountll(pre); \
      T += (i128)(Sj*(i64)(2*nb-15) - QT4[st][nb]); } \
    i64 S = s + 4*(K) - __builtin_popcountll(Q); \
    i128 dd = ((i128)d<<(K)) - T; \
    i128 lim2=(i128)S-G; if((unsigned __int128)(dd+lim2) > (unsigned __int128)(2*lim2)) break; \
    d=(i64)dd; s=S; rH=H/(double)s; i+=(K); n++; \
  } \
  *pd=d; *ps=s; *pi=i; return n; }
FASTRUN(8) FASTRUN(12) FASTRUN(16) FASTRUN(20) FASTRUN(24) FASTRUN(28) FASTRUN(32) FASTRUN(36) FASTRUN(40) FASTRUN(44) FASTRUN(48)

static void pr(FILE*f,i128 x){char s[50];int i=49;s[i]=0;if(x<0){fputc('-',f);x=-x;} if(!x){fputs("0",f);return;}while(x){s[--i]='0'+(int)(x%10);x/=10;}fputs(s+i,f);}

static u64 cnt[8]; static const char*nm[8]={"ge","de","do","p1","p2","p3","b2","H"};
static u64 nearc[9][2];
static int halted=0;

/* one visit with the full rules (as abrun.c, without steps); returns 1 on halt */
static int exact1(u64 i, i64*pa, i64*pb){
  i64 a=*pa,b=*pb; int r;
  if(b>a && b-a<=8){ int g=(int)(b-a); nearc[g][a&1]++;
    printf("near i=%llu g=%d par=%d a=%lld b=%lld\n",i,g,(int)(a&1),a,b); fflush(stdout);}
  if(b==3){ printf("HALT at i=%llu a=%lld\n",i,a); fflush(stdout); cnt[7]++; return 1; }
  else if(b==2){ a-=3; b=7; r=6; }
  else if(a>=b){ a=a-b+1; b=2*b+3; r=0; }
  else if(b==a+1){ b=2*a+4; a=4; r=3; }
  else if(b==a+2){ b=2*a+7; a=1; r=4; }
  else if((a&1) && b==a+3){ a=2*a+1; b=9; r=5; }
  else if(!(a&1)){ b=b-a-1; a=2*a+4; r=1; }
  else { b=b-a; a=2*a+3; r=2; }
  if(r>=3){ printf("reset i=%llu %s new a=%lld b=%lld\n",i,nm[r],a,b); fflush(stdout); }
  cnt[r]++; *pa=a; *pb=b; return 0;
}

int main(int argc,char**argv){
  if(argc<2){fprintf(stderr,"usage: abfast N [logevery [i0 a b]]\n");return 1;}
  u64 N=strtoull(argv[1],0,10), LE=argc>2?strtoull(argv[2],0,10):0;
  i64 a=2,b=9; u64 i=0;
  if(argc>5){ i=strtoull(argv[3],0,10); a=strtoll(argv[4],0,10); b=strtoll(argv[5],0,10); }
  mktab();
  u64 nfast=0, nslow=0; u64 nextlog = LE? (i/LE+1)*LE : ~0ULL;
  i64 s=a+b, d=b-a;
  while(i<N){
    /* block length: a multiple of 4 with G = 32 * 2^K at most s / 64 (rejections at most about 1 in 64), at most 48 */
    int K = 0; { int lg = 63 - __builtin_clzll((u64)s); K = ((lg - 11) / 4) * 4; if(K < 8) K = 0; if(K > 48) K = 48; }
    while(K && (i+K>N || i+K>nextlog)) K-=4;
    if(K<8) K=0;   /* do not run past N or a log point */
    if(K>=8 && i+K<=N && i+K<=nextlog){
      u64 lim = N<nextlog? N : nextlog, nb=0;
      switch(K){
#define CASE(k) case k: nb=fastrun##k(&d,&s,&i,lim); break;
        CASE(8) CASE(12) CASE(16) CASE(20) CASE(24) CASE(28) CASE(32) CASE(36) CASE(40) CASE(44) CASE(48)
#undef CASE
      }
      nfast+=nb;
      if(i>=nextlog){ a=(s-d)/2; b=(s+d)/2;
        printf("prog i=%llu a=%lld b=%lld fast=%llu slow=%llu\n",i,a,b,nfast,nslow); fflush(stdout);
        nextlog=(i/LE+1)*LE; }
      if(nb) continue;   /* recompute K; a block that was refused goes to the code below */
    }
    /* slow block: one visit at a time */
    a=(s-d)/2; b=(s+d)/2; nslow++;
    u64 end = i+(K?K:32)<N? i+(K?K:32) : N;
    for(;i<end;i++){
      if(exact1(i,&a,&b)){ halted=1; break; }
      if(i+1>=nextlog){ printf("prog i=%llu a=%lld b=%lld fast=%llu slow=%llu\n",i+1,a,b,nfast,nslow); fflush(stdout);
        nextlog=((i+1)/LE+1)*LE; }
    }
    if(halted) break;
    if(a>((i64)1<<60)||b>((i64)1<<60)){ printf("overflow guard at i=%llu\n",i); break; }
    s=a+b; d=b-a;
  }
  a=(s-d)/2; b=(s+d)/2;
  if(!halted) printf("final i=%llu a=%lld b=%lld\n",i,a,b);
  printf("fast blocks %llu, slow blocks %llu\n",nfast,nslow);
  printf("swap %llu (fast blocks not split by rule)\n",cnt[0]);
  for(int k=1;k<8;k++) printf("%s %llu\n",nm[k],cnt[k]);
  for(int g=1;g<=8;g++) printf("near g=%d even %llu odd %llu\n",g,nearc[g][0],nearc[g][1]);
  return 0;
}
