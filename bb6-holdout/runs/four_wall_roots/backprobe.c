/* untrusted probe; build: cp ../../blankrun/fast.h . && gcc -O2 -w -o backprobe backprobe.c; run: ./backprobe K WMAX */
/* small-width probe: the full round map on every round start G1 + up to K-1 marks of width <= WMAX, then for every
   three-wall round start: how deep its backward tree goes, and whether it reaches a clean tape. */
#include <stdio.h>
#include <stdlib.h>
#include "fast.h"
#define MAXK 7
typedef struct { unsigned char k, t[MAXK]; short p[MAXK]; short w; } St;
static int K, WMAX;
static St *src, *dst; static long ns, cap;
static int eqst(St*a, St*b){ if(a->k!=b->k||a->w!=b->w) return 0; for(int i=0;i<a->k;i++) if(a->t[i]!=b->t[i]||a->p[i]!=b->p[i]) return 0; return 1; }
static unsigned long hs(St*a){ unsigned long h=a->k*1000003UL+a->w; for(int i=0;i<a->k;i++) h=h*1315423911UL+a->t[i]*7919+a->p[i]; return h; }
static St cur; static int ct[MAXK]; static short cp[MAXK];
static void runone(int w, int k){
  set_start(w); for(int i=0;i<k;i++) add_mark(ct[i], cp[i]); halted=bad=0; nend=0; do_round();
  if(halted||bad) return; if(nm>MAXK) return; ll W2=realW(); if(W2>32000) return;
  if(ns>=cap){cap=cap?cap*2:1<<20; src=realloc(src,cap*sizeof(St)); dst=realloc(dst,cap*sizeof(St));}
  St a={0}, b={0}; a.k=k; a.w=w; for(int i=0;i<k;i++){a.t[i]=ct[i];a.p[i]=cp[i];}
  b.k=nm; b.w=W2; for(int i=0;i<nm;i++){b.t[i]=MT(i); b.p[i]=realP(i);} src[ns]=a; dst[ns]=b; ns++;
}
static void gen(int w, int i, int k, int from){
  if(i==k){ runone(w,k); return; }
  for(int t=0;t<4;t++){ int L=MLEN[t]; for(int p=from;p+L<=w;p++){ ct[i]=t; cp[i]=p; gen(w,i+1,k,p+L); } }
}
/* hash index on dst */
static long *hh; static long hcap;
static void build(){ hcap=1; while(hcap<4*ns) hcap<<=1; hh=malloc(hcap*sizeof(long)); for(long i=0;i<hcap;i++) hh[i]=-1;
  /* chained by open addressing over entries, multiple per key */
  for(long i=0;i<ns;i++){ unsigned long h=hs(&dst[i])&(hcap-1); while(hh[h]>=0) h=(h+1)&(hcap-1); hh[h]=i; } }
static int clean(St*a){ return a->k==2&&a->t[1]==tM&&a->p[1]==a->w-2; }
static long visited; static int maxd; static int reach_clean;
static void back(St*a, int d){ visited++; if(d>maxd)maxd=d; if(clean(a)){reach_clean=1; return;} if(visited>100000) return;
  unsigned long h=hs(a)&(hcap-1); while(hh[h]>=0){ long j=hh[h]; if(eqst(&dst[j],a)) back(&src[j],d+1); h=(h+1)&(hcap-1);} }
int main(int c,char**v){ K=atoi(v[1]); WMAX=atoi(v[2]);
  for(int w=6; w<=WMAX; w++) for(int k=1;k<=K;k++){ ct[0]=tG; cp[0]=1; gen(w,1,k,4); }
  fprintf(stderr,"transitions %ld\n",ns); build();
  /* three-wall targets: those among dst with width <= WMAX - 0 (complete preimages need preimage width < target width <= WMAX) */
  int dh[64]={0}; long nt=0, nc=0, n0=0, big=0;
  for(int w=20; w<=WMAX; w++) for(int a=4;a<w;a++) for(int b=a+2;b<w;b++) for(int cc=b+2;cc+2<=w;cc++){
    St t={0}; t.k=4; t.w=w; t.t[0]=tG;t.p[0]=1; t.t[1]=tW;t.p[1]=a; t.t[2]=tW;t.p[2]=b; t.t[3]=tW;t.p[3]=cc;
    visited=0; maxd=0; reach_clean=0; back(&t,0); nt++; if(reach_clean) nc++; if(visited==1) n0++; if(visited>100000) big++;
    if(maxd<64) dh[maxd]++; }
  printf("K %d WMAX %d targets %ld reach-clean %ld no-preimage %ld huge %ld\n",K,WMAX,nt,nc,n0,big);
  for(int i=0;i<64;i++) if(dh[i]) printf(" depth %d: %d\n",i,dh[i]);
}
