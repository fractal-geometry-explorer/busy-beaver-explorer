// 1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA (129887): an exact accelerated run on the stack model of py/model.py.
//
// The tape is  0^inf [1^n1 0^z1] ... [1^nk 0^zk]  (the frames)  followed by one of
//   RET(q, v):  1^(q-1) C>1 :: v        Z(v): C on the last zero of the top frame, :: v        CALL(m, X): 1^m B> X
// where v and X are words over b = 110 and c = 111, ":: v" stands for the cells v0, 1 1 v1, 1 1 v2, ... and X for
// 1 1 x0, 1 1 x1, ..., both followed by blank tape.  The machine halts exactly in RET(1, v) on a top frame "1 0"
// (n = 1, z = 1).  A *visit* is RET(1, v) with no frame; two steps later the head is in B on a blank cell with
// blank tape on its left and the word v on its right.  Words are run-length coded with a third letter a = cbb,
// frames too, and every transition adds its exact number of machine steps.  The transitions are those of
// py/model.py, with two calls in a row taken as one where no visit falls in between:
//   CALL(m, b R) -> RET(m-1, c c R),   CALL(m, c^j b c^i b Z) -> push (m-1, 3j-1), CALL(3i+8, Z),   and so on.
//
//   wrun run MAXVISITS [EVERY]      the run from blank tape: a line at every power of two (and every EVERY) visits,
//                                   at every visit that reached the right end, and at every near miss
//   wrun dump MAXVISITS             "visit step hash tokens" for every visit, to compare with c/dvis.c
//   wrun word WORD [MAXVISITS]      the run from the visit on WORD (letters b, c)
//   wrun enum L                     the first visit on every word of L tokens: which ones halt
//   wrun mc SEED TRIALS L VISITS    random words of L tokens, VISITS visits each: how many halt
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef int64_t i64; typedef __int128 i128;
#define CAP (1L<<27)
#define INF ((i64)1<<62)
static char *ws; static i64 *wc; static long wn; static i64 tot;      // the word: runs of a, b, c; the front is on top
static i64 *sn, *sz, *sc; static long stn;                             // the frames: runs of equal (n, z)
static i128 steps;
static i64 g_vis, g_ends, g_endvis, g_near; static int quiet, dump; static i64 every;
static void die(const char*m){ fprintf(stderr,"%s\n",m); exit(1); }
static inline void push_run(char s,i64 k){ if(wn&&ws[wn-1]==s) wc[wn-1]+=k; else { if(wn>=CAP) die("word cap"); ws[wn]=s; wc[wn]=k; wn++; } }
static inline void unpack(void){                       // a front run a^k becomes c b b a^(k-1)
  if(wn&&ws[wn-1]=='a'){ if(--wc[wn-1]==0) wn--; push_run('b',2); push_run('c',1); } }
static inline void pre_b(i64 k){ if(k<=0) return; tot+=k; push_run('b',k); }
static inline void pre_c(i64 k){ tot+=k;               // a c-run never stands directly in front of an a-run
  if(wn&&ws[wn-1]=='a') unpack();
  if(k==1&&wn&&ws[wn-1]=='b'&&wc[wn-1]>=2){ wc[wn-1]-=2; if(wc[wn-1]==0) wn--; push_run('a',1); return; }
  push_run('c',k); }
static inline i64 lead(void){ unpack(); if(wn&&ws[wn-1]=='c'){ wn--; tot-=wc[wn]; return wc[wn]; } return 0; }
static inline int popb(void){ if(!wn) return 0; if(--wc[wn-1]==0) wn--; tot--; return 1; }   // the front is a b
static inline void split_top(void){ if(sc[stn-1]>1){ sc[stn-1]--; sn[stn]=sn[stn-1]; sz[stn]=sz[stn-1]; sc[stn]=1; stn++; } }
static inline void push_frame(i64 n,i64 z,i64 k){
  if(stn>1&&sn[stn-1]==n&&sz[stn-1]==z&&z==2) sc[stn-1]+=k; else { if(stn>=CAP) die("stack cap"); sn[stn]=n; sz[stn]=z; sc[stn]=k; stn++; } }
static inline void leave(i64 m,i64 z){                 // CALL(m, ..) leaves m-1 ones and z zeros behind
  if(m==1){ split_top(); sz[stn-1]+=z; } else push_frame(m-1,z,1); }
static void pr128(i128 x){ char b[50]; int i=49; b[i]=0; if(x<0){ putchar('-'); x=-x; } if(!x) b[--i]='0'; while(x){ b[--i]='0'+(int)(x%10); x/=10; } fputs(b+i,stdout); }
static uint64_t whash(void){ uint64_t h=1469598103934665603ULL;
  for(long r=wn-1;r>=0;r--) for(i64 k=0;k<wc[r];k++){ const char*t= ws[r]=='a'?"cbb":ws[r]=='b'?"b":"c"; for(;*t;t++){ h^=(unsigned char)*t; h*=1099511628211ULL; } }
  return h; }

// runs from RET(1, word) with no frame, `steps` set by the caller; returns 1 on a halt, 0 after maxvis visits
static int run(double maxvis){
  stn=1; sn[0]=0; sz[0]=INF; sc[0]=1;
  int mode=0; i64 q=1, vis=0, ms=0, ends=0, lastend=0, near=0;
  for(;;){ ms++;
    if(mode==0){                                                                  // RET(q, v)
      if(q>=4){ i64 t=(q-1)/3; q-=3*t; pre_b(t); steps+=5*(i128)t; continue; }
      if(q==3){ pre_b(1); steps+=5; mode=1; continue; }
      if(q==2){ split_top(); pre_b(1); steps+=3; if(sz[stn-1]>=2){ sz[stn-1]--; mode=1; } else { q=sn[--stn]; } continue; }
      if(stn==1){ vis++;
        if(dump){ printf("%ld ",(long)vis); pr128(steps+2); printf(" %016lx %ld\n",(unsigned long)whash(),(long)tot); }
        else if(!quiet){
          if(lastend==vis-1&&vis>1) printf("  visit %ld reached the right end\n",(long)vis-1);
          if((vis&(vis-1))==0||vis>=maxvis||(every&&vis%every==0)){ printf("visit %ld at step ",(long)vis); pr128(steps+2);
            printf(": %ld tokens in %ld runs; model steps %ld; the right end reached in %ld visits; near misses %ld\n",(long)tot,wn,(long)ms,(long)g_endvis,(long)near); fflush(stdout); } }
        if(vis>=maxvis){ g_vis=vis; g_ends=ends; return 0; } }
      i64 n=sn[stn-1], z=sz[stn-1];
      if(n==1&&stn>1){ near++; g_near++; if(!quiet&&!dump) printf("  near miss in visit %ld: RET(1) on a frame with a single 1 and %ld zeros (a halt needs 1)\n",(long)vis,(long)z); }
      if(z==2){ i64 k=sc[stn-1];
        if(n==7){ stn--; pre_c(1); if(k>1){ tot+=3*(k-1); push_run('a',k-1); } pre_b(2); steps+=13*(i128)k; continue; }   // k frames (7, 2) at once
        split_top(); stn--; pre_c(1); q=n; steps+=3; continue; }
      split_top();
      if(z>=3){ pre_c(1); sz[stn-1]-=2; mode=1; steps+=3; continue; }
      stn--;                                                                      // z == 1
      if(n==1){ g_vis=vis; g_ends=ends; if(!quiet){ printf("HALT in visit %ld, at step ",(long)vis); pr128(steps+4); printf(" (model step %ld)\n",(long)ms); } return 1; }
      if(n==2){ split_top(); sz[stn-1]++; } else { sn[stn]=n-2; sz[stn]=1; sc[stn]=1; stn++; }
      steps+=5; mode=2; q=1; continue; }
    if(mode==1){                                                                  // Z(v)
      i64 e=0; split_top(); if(--sz[stn-1]==0) e=sn[--stn];
      i64 a=lead(); if(popb()){ q=e+3*a+2; steps+=3*(i128)a+2; } else { q=e+3*a; steps+=3*(i128)a; } mode=2; continue; }
    // CALL(q, X)
    if(q==1&&stn==1&&wn){                             // on the empty stack with m = 1 the call passes through a visit:
      i64 j=lead();                                   // CALL(1, c^j b Y) -> RET(1, c Y) [9j+7], CALL(1, c^j) -> RET(1, c) [9j+1]
      if(popb()) steps+=9*(i128)j+7; else { ends++; if(lastend!=vis){ g_endvis++; lastend=vis; } steps+=9*(i128)j+1; }
      pre_c(1); mode=0; continue; }
    if(!wn){ ends++; if(lastend!=vis){ g_endvis++; lastend=vis; } mode=0; pre_c(1); steps+=1; continue; }
    if(ws[wn-1]=='b'){ popb(); pre_c(2); steps+=10; if(q>=2){ mode=0; q--; } else mode=1; continue; }
    if(ws[wn-1]=='a'){ i64 k=wc[wn-1]; wn--; tot-=3*k; leave(q,2); if(k>1) push_frame(7,2,k-1); steps+=27*(i128)k; q=8; continue; }   // a^k at once
    i64 j=lead();
    if(!wn){ ends++; if(lastend!=vis){ g_endvis++; lastend=vis; } steps+=9*(i128)j+10; if(j==1){ q+=5; continue; } leave(q,3*j-3); q=6; continue; }
    popb(); leave(q,3*j-1);
    i64 i=lead();
    if(popb()){ q=3*i+8; steps+=9*(i128)j+3*(i128)i+18; }
    else { ends++; if(lastend!=vis){ g_endvis++; lastend=vis; } q=3*i+6; steps+=9*(i128)j+3*(i128)i+16; }
  }
}

int main(int argc,char**argv){
  if(argc<3) die("usage: wrun run MAXVISITS [EVERY] | dump MAXVISITS | word WORD [MAXVISITS] | enum L | mc SEED TRIALS L VISITS");
  ws=malloc(CAP); wc=malloc(CAP*8); sn=malloc(CAP*8); sz=malloc(CAP*8); sc=malloc(CAP*8);
  if(!ws||!wc||!sn||!sz||!sc) die("memory");
  const char*cmd=argv[1];
  if(!strcmp(cmd,"run")||!strcmp(cmd,"dump")){        // from blank tape: A>0, B>0 give RET(1, c) at step 2
    dump=!strcmp(cmd,"dump"); every=argc>3?atol(argv[3]):0; wn=0; tot=0; pre_c(1); steps=2; run(atof(argv[2])); return 0; }
  if(!strcmp(cmd,"word")){                            // RET(1, w) is two steps before the visit on w
    const char*w=argv[2]; long L=strlen(w); wn=0; tot=0; for(long i=L-1;i>=0;i--){ if(w[i]=='b') pre_b(1); else pre_c(1); }
    steps=-2; run(argc>3?atof(argv[3]):1e18); return 0; }
  if(!strcmp(cmd,"enum")){ quiet=1; long L=atol(argv[2]), halts=0;
    for(unsigned long x=0;x<(1UL<<L);x++){ wn=0; tot=0; for(long i=0;i<L;i++){ if((x>>i)&1) pre_c(1); else pre_b(1); }
      steps=-2; if(run(2)){ halts++; if(halts<=20){ for(long i=L-1;i>=0;i--) putchar((x>>i)&1?'c':'b'); printf(" halts at step "); pr128(steps+4); putchar('\n'); } } }
    printf("%ld tokens: %lu words, %ld halt during the first visit\n",L,1UL<<L,halts); return 0; }
  if(!strcmp(cmd,"mc")){ if(argc<6) die("mc SEED TRIALS L VISITS"); quiet=1; srand48(atol(argv[2])); long trials=atol(argv[3]), L=atol(argv[4]), halts=0; double V=atof(argv[5]); i64 EV=0, VV=0; g_near=0;
    for(long t=0;t<trials;t++){ wn=0; tot=0; for(long i=0;i<L;i++){ if(drand48()<0.5) pre_b(1); else pre_c(1); }
      g_endvis=0; steps=-2; halts+=run(V); EV+=g_endvis; VV+=g_vis; }
    printf("%ld random words of %ld tokens, up to %g visits each: %ld halted; %ld visits in all, %ld of them reached the right end; RET(1) met a frame with a single 1 %ld times\n",trials,L,V,halts,(long)VV,(long)EV,(long)g_near); return 0; }
  die("unknown command");
}
