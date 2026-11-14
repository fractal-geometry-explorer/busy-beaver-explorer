// Exact Turing machine simulator: runs of words, context-carrying shift rules found on the fly, and jumps over
// linear regimes (cycles), with arbitrary-size counts.  See accsim.c for the first two; this file adds:
//
// * every run count, the event count and the step count are big integers (NL limbs of 64 bits);
// * cycle jumps: every PERIOD events (an event is the head on a new leftmost cell; the left stack is then empty)
//   the tape is sampled as its sequence of items.  If HW = 14 consecutive samples have the same items and state,
//   every run count moves by a constant d per sample (13 equal differences) and the number of steps per cycle moves
//   by a constant b, then the next k cycles do the same, for k = the largest number that keeps every decreasing
//   count at or above MARGIN words: the counts become cnt + k*d and k*D + b*k(k-1)/2 steps are added (D the length
//   of the next cycle).  Reason: between samples the machine touches a long run only by crossing it with a shift
//   rule (period at most JMAX = 4 words, so 12 = lcm(1..4) consecutive cycles cover every residue of every count)
//   or by reading at most K+WL cells into it, and MARGIN words are more than that.
//   The jumps are validated against the simulator without them (accsim.c): same step counts at the same events.
//
// usage: accbig MACHINE PERIOD MAXJUMPS periods...          e.g. accbig M 160 100000 3 11
// environment: TARGET=events (stop exactly there, for validation; only below 2^63), VERB=1 (print every cycle jump)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128;
#ifndef NL
#define NL 160
#endif
typedef struct { int n; uint64_t w[NL]; } Big;
static void big_fail(void){ printf("BIGNUM OVERFLOW (more than %d limbs)\n",NL); exit(2); }
static inline void big_setu(Big*a,uint64_t v){ a->n= v?1:0; a->w[0]=v; }
static inline int big_isu(const Big*a){ return a->n<=1; }
static inline uint64_t big_u(const Big*a){ return a->n? a->w[0]:0; }
static void big_addu(Big*a,uint64_t v){ int i=0; while(v){ if(i==a->n){ if(i==NL)big_fail(); a->w[i]=0; a->n++; } uint64_t s=a->w[i]+v; v=(s<v); a->w[i]=s; i++; } }
static void big_subu(Big*a,uint64_t v){ int i=0; while(v){ if(i>=a->n){ printf("big_subu underflow\n"); exit(3);} uint64_t o=a->w[i]; a->w[i]=o-v; v=(o<v); i++; } while(a->n>0&&a->w[a->n-1]==0)a->n--; }
static void big_add(Big*a,const Big*b){ uint64_t c=0; int i; for(i=0;i<b->n||c;i++){ if(i==a->n){ if(i==NL)big_fail(); a->w[i]=0; a->n++; } uint64_t x=a->w[i], y=(i<b->n?b->w[i]:0); uint64_t s=x+y; uint64_t c2=(s<x); s+=c; c2|=(s<c); a->w[i]=s; c=c2; } }
static int big_cmp(const Big*a,const Big*b){ if(a->n!=b->n) return a->n<b->n?-1:1; for(int i=a->n-1;i>=0;i--) if(a->w[i]!=b->w[i]) return a->w[i]<b->w[i]?-1:1; return 0; }
static void big_sub(Big*a,const Big*b){ if(big_cmp(a,b)<0){ printf("big_sub underflow\n"); exit(3);} uint64_t br=0; for(int i=0;i<a->n;i++){ uint64_t x=a->w[i], y=(i<b->n?b->w[i]:0); uint64_t d=x-y; uint64_t b2=(x<y); uint64_t d2=d-br; b2|=(d<br); a->w[i]=d2; br=b2; } while(a->n>0&&a->w[a->n-1]==0)a->n--; }
static void big_mulu(Big*r,const Big*a,uint64_t m){ uint64_t c=0; int i; for(i=0;i<a->n;i++){ u128 p=(u128)a->w[i]*m+c; r->w[i]=(uint64_t)p; c=(uint64_t)(p>>64); } r->n=a->n; if(c){ if(r->n==NL)big_fail(); r->w[r->n++]=c; } if(m==0)r->n=0; }
static uint64_t big_divu(Big*q,const Big*a,uint64_t d){ u128 r=0; q->n=a->n; for(int i=a->n-1;i>=0;i--){ u128 cur=(r<<64)|a->w[i]; q->w[i]=(uint64_t)(cur/d); r=cur%d; } while(q->n>0&&q->w[q->n-1]==0)q->n--; return (uint64_t)r; }
static void big_mul(Big*r,const Big*a,const Big*b){ static uint64_t t[2*NL+2]; int n=a->n+b->n; if(a->n==0||b->n==0){ r->n=0; return; } memset(t,0,sizeof(uint64_t)*(n+1));
  for(int i=0;i<a->n;i++){ uint64_t c=0; for(int j=0;j<b->n;j++){ u128 p=(u128)a->w[i]*b->w[j]+t[i+j]+c; t[i+j]=(uint64_t)p; c=(uint64_t)(p>>64); } t[i+b->n]+=c; }
  while(n>0&&t[n-1]==0)n--; if(n>NL)big_fail(); memcpy(r->w,t,sizeof(uint64_t)*n); r->n=n; }
static void big_print(const Big*a){ static Big t,q; static char buf[20*NL+40]; int pos=sizeof(buf)-1; buf[pos]=0; t=*a; if(t.n==0){ fputs("0",stdout); return; }
  while(t.n>0){ uint64_t r=big_divu(&q,&t,10000000000000000000ULL); t=q; for(int k=0;k<19;k++){ buf[--pos]='0'+(int)(r%10); r/=10; if(t.n==0&&r==0)break; } }
  while(buf[pos]=='0'&&buf[pos+1])pos++; fputs(buf+pos,stdout); }
static int big_digits(const Big*a){ if(a->n==0) return 1; double l=0; l=(a->n-1)*64*0.30102999566398; uint64_t top=a->w[a->n-1]; int b=0; while(top){b++;top>>=1;} return (int)(l+b*0.30102999566398)+1; }

#define MAXW 4096
#define WL 48
#define K 40
#define JMAX 4
static unsigned char words[MAXW][WL]; static int wlen[MAXW]; static int nwords=0;
static int word_id(const unsigned char*c,int L){ for(int i=0;i<nwords;i++) if(wlen[i]==L&&!memcmp(words[i],c,L)) return i;
  if(nwords>=MAXW){fprintf(stderr,"too many words\n");exit(1);} memcpy(words[nwords],c,L); wlen[nwords]=L; return nwords++; }
// pool of run counts
#define POOL 65536
static Big *pool; static int pfree[POOL]; static int npfree=0;
static int palloc(void){ if(npfree==0){ printf("pool exhausted\n"); exit(4);} return pfree[--npfree]; }
static void pfree_(int i){ pfree[npfree++]=i; }
typedef struct { int32_t wid; int32_t v; } Item;   // wid<0: one cell with value v; else a run of word wid, count pool[v]
typedef struct { Item*a; long n,cap; long ex; int dir; long thr; } Stack;
static Stack SL,SR;
static int nper; static int pers[8];
static void grow(Stack*s){ if(s->n+WL+4>=s->cap){ s->cap*=2; s->a=realloc(s->a,s->cap*sizeof(Item)); if(!s->a){fprintf(stderr,"memory\n");exit(1);} } }
static inline void raw_push(Stack*s,int c){ grow(s); s->a[s->n].wid=-1; s->a[s->n].v=c; s->n++; s->ex++; }
static void push_run(Stack*s,int wid,const Big*cnt){ grow(s); if(s->n>0&&s->a[s->n-1].wid==wid){ big_add(&pool[s->a[s->n-1].v],cnt); } else { int p=palloc(); pool[p]=*cnt; s->a[s->n].wid=wid; s->a[s->n].v=p; s->n++; } s->ex=0; }
static void push_run_u(Stack*s,int wid,uint64_t c){ Big b; big_setu(&b,c); push_run(s,wid,&b); }
static inline int word_cell(const Stack*s,int wid,int k){ return s->dir==0 ? words[wid][wlen[wid]-1-k] : words[wid][k]; }
static void compress(Stack*s){
  for(int pi=0;pi<nper;pi++){ int L=pers[pi];
    if(s->ex==L && s->n>L && s->a[s->n-L-1].wid>=0 && wlen[s->a[s->n-L-1].wid]==L){
      int wid=s->a[s->n-L-1].wid; int ok=1; for(int k=0;k<L&&ok;k++) if(s->a[s->n-1-k].v!=word_cell(s,wid,k)) ok=0;
      if(ok){ s->n-=L; big_addu(&pool[s->a[s->n-1].v],1); s->ex=0; return; } }
    int need=(L<8?4:2)*L;
    if(s->ex>=need){ int ok=1; for(int k=0;k<need-L&&ok;k++) if(s->a[s->n-1-k].v!=s->a[s->n-1-k-L].v) ok=0;
      if(ok){ unsigned char c[WL]; for(int k=0;k<L;k++){ int v=s->a[s->n-1-k].v; if(s->dir==0) c[L-1-k]=v; else c[k]=v; }
        int wid=word_id(c,L); s->n-=need; push_run_u(s,wid,need/L); return; } }
  }
}
#define KEEP 24
static unsigned char sbuf[1<<20];
static void sweep(Stack*s){
  long m=0; while(s->n>0&&s->a[s->n-1].wid<0&&m<(long)sizeof(sbuf)){ sbuf[m++]=(unsigned char)s->a[s->n-1].v; s->n--; }
  long i=m-1; s->ex=0;
  while(i>=KEEP){ int done=0;
    for(int pi=0;pi<nper&&!done;pi++){ int L=pers[pi]; int minr=(L<8?4:2); long r=1;
      if(i-KEEP+1<(long)minr*L) continue;
      while(i-(r+1)*L+1>=KEEP){ int ok=1; for(int k=0;k<L&&ok;k++) if(sbuf[i-k]!=sbuf[i-r*L-k]) ok=0; if(!ok)break; r++; }
      if(r>=minr){ unsigned char c[WL]; for(int k=0;k<L;k++){ if(s->dir==0) c[k]=sbuf[i-k]; else c[L-1-k]=sbuf[i-k]; }
        push_run_u(s,word_id(c,L),r); i-=r*L; done=1; } }
    if(!done){ raw_push(s,sbuf[i]); i--; } }
  while(i>=0){ raw_push(s,sbuf[i]); i--; }
}
static inline void push(Stack*s,int c){ raw_push(s,c); if(s->ex>=3) compress(s); if(++s->thr>=2048){ sweep(s); s->thr=0; } }
static void expand(Stack*s){ Item*t=&s->a[s->n-1]; int wid=t->wid; int L=wlen[wid]; Big*c=&pool[t->v]; big_subu(c,1); if(c->n==0){ pfree_(t->v); s->n--; }
  grow(s); for(int k=L-1;k>=0;k--){ s->a[s->n].wid=-1; s->a[s->n].v=word_cell(s,wid,k); s->n++; } s->ex=L; }
static inline int raw_pop(Stack*s){ if(s->n==0) return 0; if(s->a[s->n-1].wid>=0) expand(s); s->n--; if(s->ex>0)s->ex--; return s->a[s->n].v; }
static void peek(const Stack*s,int k,unsigned char*out){
  long i=s->n-1; int got=0; while(got<k){ if(i<0){ out[got++]=0; continue; } const Item*t=&s->a[i];
    if(t->wid<0){ out[got++]=(unsigned char)t->v; i--; } else { int L=wlen[t->wid]; const Big*c=&pool[t->v]; uint64_t lim= (c->n>1||c->w[0]>1000)? 1000*(uint64_t)L : c->w[0]*L; uint64_t j=0; while(got<k&&j<lim){ out[got++]=word_cell(s,t->wid,(int)(j%L)); j++; } i--; } } }
typedef struct { int active; long q; long height; int wid; int st; unsigned char ctx[K]; long reach; uint64_t raw0; } Probe;
static Probe PL,PR;
#define MAXR 1024
#define HW 14
#define MARGIN 64
typedef struct { uint64_t hash; int nr; int st,cur; Big steps; } Sample;
static Sample hist[HW]; static Big *hptr[HW]; static int nh=0;   // hptr[i][r]: the run counts of sample i
static int g_s,g_cur;
static void dump(FILE*f){ for(int side=0;side<2;side++){ Stack*st=side?&SR:&SL; if(side) fprintf(f," [%c>%d] ",'A'+g_s,g_cur);
  for(long i=side?st->n-1:0; side? i>=0 : i<st->n; i+=side?-1:1){ Item*t=&st->a[i]; if(t->wid<0) fputc('0'+t->v,f); else { fputc('(',f); for(int k=0;k<wlen[t->wid];k++)fputc('0'+words[t->wid][k],f); fputs(")^",f); if(f==stdout) big_print(&pool[t->v]); else fprintf(f,"%d digits",big_digits(&pool[t->v])); fputc(' ',f);} } } fputc('\n',f); }
int main(int argc,char**argv){
  const char*m=argv[1]; long PERIOD=atol(argv[2]); long maxj=atol(argv[3]); nper=0; for(int i=4;i<argc&&nper<8;i++) pers[nper++]=atoi(argv[i]);
  uint64_t TARGET=0; if(getenv("TARGET")) TARGET=strtoull(getenv("TARGET"),0,10); int verb=getenv("VERB")!=0;
  int W[6][2],D[6][2],S[6][2];
  for(int i=0;i<6;i++)for(int b=0;b<2;b++){const char*p=m+7*i+3*b; if(p[0]=='-'){S[i][b]=-1;continue;} W[i][b]=p[0]-'0';D[i][b]=(p[1]=='R')?1:-1;S[i][b]=p[2]-'A';}
  pool=malloc(sizeof(Big)*POOL); for(int i=POOL-1;i>=0;i--) pfree[npfree++]=i;
  for(int i=0;i<HW;i++) hptr[i]=malloc(sizeof(Big)*MAXR);
  SL.cap=SR.cap=1<<16; SL.a=malloc(SL.cap*sizeof(Item)); SR.a=malloc(SR.cap*sizeof(Item)); SL.dir=0; SR.dir=1; SL.thr=SR.thr=0;
  int cur=0,s=0; long pos=0; Big steps,ev; big_setu(&steps,0); big_setu(&ev,0); uint64_t raw=0, rawfold=0; long evmod=0; long jumps=0,cyc=0; uint64_t rawtotal=0;
  #define FOLD() do{ big_addu(&steps,raw-rawfold); rawfold=raw; }while(0)
  for(;;){
    if(S[s][cur]<0){ FOLD(); big_addu(&steps,1); printf("HALT in state %c reading %d after ",'A'+s,cur); big_print(&steps); printf(" steps (the halting step counted); event "); big_print(&ev); printf("; %ld cycle jumps, %ld shift jumps\n",cyc,jumps); g_s=s; g_cur=cur; if(SL.n+SR.n<4000) dump(stdout); return 0; }
    int w=W[s][cur], d=D[s][cur]; s=S[s][cur]; raw++;
    if(d>0){
      push(&SL,w); pos++;
      if(SR.n>0&&SR.a[SR.n-1].wid>=0){
        Item*t=&SR.a[SR.n-1]; int L=wlen[t->wid]; int keep=0;
        if(PR.active&&PR.height==SR.n&&PR.wid==t->wid&&pos>PR.q&&(pos-PR.q)%L==0&&(pos-PR.q)/L<=JMAX){
          int jj=(int)((pos-PR.q)/L);
          if(PR.st!=s){ if(jj<JMAX) keep=1; }
          else { int b=(int)(PR.q-PR.reach); unsigned char c[K];
            if(b<=K-1&&jj*L<=WL){ peek(&SL,b,c); int ok=1; for(int k=0;k<b&&ok;k++) if(c[k]!=PR.ctx[k]) ok=0;
              Big mm; uint64_t rem=big_divu(&mm,&pool[t->v],jj);
              if(ok&&mm.n>0){ uint64_t delta=raw-PR.raw0; unsigned char cx[K],dd[WL]; int LL=jj*L; int rv=t->v;
                for(int k=0;k<b;k++) cx[k]=raw_pop(&SL);
                for(int k=0;k<LL;k++) dd[LL-1-k]=raw_pop(&SL);
                Big m1=mm; big_addu(&m1,1); push_run(&SL,word_id(dd,LL),&m1);
                for(int k=b-1;k>=0;k--) raw_push(&SL,cx[k]);
                t=&SR.a[SR.n-1]; if(rem==0){ pfree_(rv); SR.n--; } else big_setu(&pool[rv],rem); SR.ex=0;
                FOLD(); Big add; big_mulu(&add,&mm,delta); big_add(&steps,&add); jumps++; PL.active=0; PR.active=0; } } }
        }
        if(!keep){ PR.active=0;
          if(SR.n>0&&SR.a[SR.n-1].wid>=0){ PR.active=1; PR.q=pos; PR.wid=SR.a[SR.n-1].wid; PR.st=s; PR.reach=pos; PR.raw0=raw; peek(&SL,K,PR.ctx); PR.height=SR.n; } }
        if(PR.active&&SR.n>0&&SR.a[SR.n-1].wid>=0&&big_isu(&pool[SR.a[SR.n-1].v])&&big_u(&pool[SR.a[SR.n-1].v])==1) PR.height=-1;
      }
      cur=raw_pop(&SR);
    } else {
      int newleft=(SL.n==0);
      push(&SR,w); pos--;
      if(SL.n>0&&SL.a[SL.n-1].wid>=0){
        Item*t=&SL.a[SL.n-1]; int L=wlen[t->wid]; int keep=0;
        if(PL.active&&PL.height==SL.n&&PL.wid==t->wid&&pos<PL.q&&(PL.q-pos)%L==0&&(PL.q-pos)/L<=JMAX){
          int jj=(int)((PL.q-pos)/L);
          if(PL.st!=s){ if(jj<JMAX) keep=1; }
          else { int b=(int)(PL.reach-PL.q); unsigned char c[K];
            if(b<=K-1&&jj*L<=WL){ peek(&SR,b,c); int ok=1; for(int k=0;k<b&&ok;k++) if(c[k]!=PL.ctx[k]) ok=0;
              Big mm; uint64_t rem=big_divu(&mm,&pool[t->v],jj);
              if(ok&&mm.n>0){ uint64_t delta=raw-PL.raw0; unsigned char cx[K],dd[WL]; int LL=jj*L; int rv=t->v;
                for(int k=0;k<b;k++) cx[k]=raw_pop(&SR);
                for(int k=0;k<LL;k++) dd[k]=raw_pop(&SR);
                Big m1=mm; big_addu(&m1,1); push_run(&SR,word_id(dd,LL),&m1);
                for(int k=b-1;k>=0;k--) raw_push(&SR,cx[k]);
                t=&SL.a[SL.n-1]; if(rem==0){ pfree_(rv); SL.n--; } else big_setu(&pool[rv],rem); SL.ex=0;
                FOLD(); Big add; big_mulu(&add,&mm,delta); big_add(&steps,&add); jumps++; PL.active=0; PR.active=0; } } }
        }
        if(!keep){ PL.active=0;
          if(SL.n>0&&SL.a[SL.n-1].wid>=0){ PL.active=1; PL.q=pos; PL.wid=SL.a[SL.n-1].wid; PL.st=s; PL.reach=pos; PL.raw0=raw; peek(&SR,K,PL.ctx); PL.height=SL.n; } }
        if(PL.active&&SL.n>0&&SL.a[SL.n-1].wid>=0&&big_isu(&pool[SL.a[SL.n-1].v])&&big_u(&pool[SL.a[SL.n-1].v])==1) PL.height=-1;
      }
      cur=raw_pop(&SL);
      if(newleft){ // an event: the head is on a new leftmost cell
        big_addu(&ev,1); evmod=(evmod+1)%PERIOD;
        if(TARGET&&big_isu(&ev)&&big_u(&ev)==TARGET){ FOLD(); printf("event %llu steps ",(unsigned long long)TARGET); big_print(&steps); printf(" cyclejumps %ld shiftjumps %ld raw %llu\n",cyc,jumps,(unsigned long long)raw); return 0; }
        if(evmod==0&&SL.n==0){
          FOLD();
          if(nh==HW){ Big*first=hptr[0]; memmove(hist,hist+1,(HW-1)*sizeof(Sample)); memmove(hptr,hptr+1,(HW-1)*sizeof(Big*)); hptr[HW-1]=first; nh--; }
          Sample*h=&hist[nh]; Big*hc=hptr[nh]; nh++;
          h->hash=1469598103934665603ULL; h->nr=0; h->st=s; h->cur=cur; h->steps=steps;
          for(long i=0;i<SR.n;i++){ Item*t=&SR.a[i]; uint64_t v= t->wid<0 ? (uint64_t)t->v : (uint64_t)(t->wid+2); h->hash=(h->hash^v)*1099511628211ULL;
            if(t->wid>=0){ if(h->nr<MAXR) hc[h->nr]=pool[t->v]; h->nr++; } }
          if(h->nr>MAXR) nh=0;
          if(nh==HW){ int ok=1; Sample*a=&hist[0];
            for(int i=1;i<HW&&ok;i++){ Sample*b=&hist[i]; if(b->hash!=a->hash||b->nr!=a->nr||b->st!=a->st||b->cur!=a->cur) ok=0; }
            static int64_t dl[MAXR]; int anydec=0; int64_t bb=0; Big Dlast;
            for(int r=0;r<a->nr&&ok;r++){ // constant small differences
              for(int i=1;i<HW&&ok;i++){ Big x; int sg=big_cmp(&hptr[i][r],&hptr[i-1][r]); int64_t d;
                if(sg>=0){ x=hptr[i][r]; big_sub(&x,&hptr[i-1][r]); if(x.n>1||(x.n==1&&x.w[0]>>62)){ok=0;break;} d=(int64_t)big_u(&x); }
                else { x=hptr[i-1][r]; big_sub(&x,&hptr[i][r]); if(x.n>1||(x.n==1&&x.w[0]>>62)){ok=0;break;} d=-(int64_t)big_u(&x); }
                if(i==1) dl[r]=d; else if(d!=dl[r]) ok=0; }
              if(ok&&dl[r]!=0){ Big mg; big_setu(&mg,MARGIN); if(big_cmp(&hptr[0][r],&mg)<0||big_cmp(&hptr[HW-1][r],&mg)<0) ok=0; if(dl[r]<0) anydec=1; } }
            if(ok){ // cycle lengths D_i = steps_i - steps_{i-1}, i=1..HW-1; second differences equal to bb
              Big Dp; int have=0;
              for(int i=1;i<HW&&ok;i++){ Big Di=hist[i].steps; big_sub(&Di,&hist[i-1].steps);
                if(have){ int sg=big_cmp(&Di,&Dp); Big x; int64_t d2; if(sg>=0){ x=Di; big_sub(&x,&Dp); if(x.n>1||(x.n==1&&x.w[0]>>62)){ok=0;break;} d2=(int64_t)big_u(&x);} else { x=Dp; big_sub(&x,&Di); if(x.n>1||(x.n==1&&x.w[0]>>62)){ok=0;break;} d2=-(int64_t)big_u(&x);} 
                  if(i==2) bb=d2; else if(d2!=bb) ok=0; }
                Dp=Di; have=1; }
              Dlast=Dp; }
            if(ok&&!anydec){ printf("NO COUNT DECREASES: the cycle of %ld events repeats for ever from event ",PERIOD); big_print(&ev); printf(" (the machine never halts if the cycle rule is right)\n"); fflush(stdout); return 0; }
            if(ok){ Big k; int havek=0;
              for(int r=0;r<a->nr;r++) if(dl[r]<0){ Big x=hptr[HW-1][r]; big_subu(&x,MARGIN); Big q; big_divu(&q,&x,(uint64_t)(-dl[r])); if(!havek||big_cmp(&q,&k)<0){ k=q; havek=1; } }
              if(TARGET&&big_isu(&ev)){ uint64_t e=big_u(&ev); if(e<TARGET){ uint64_t km=(TARGET-e)/PERIOD; if(k.n>1||big_u(&k)>km) big_setu(&k,km); } else big_setu(&k,0); }
              if(k.n>0){
                // counts
                long r=0; for(long i=0;i<SR.n;i++){ Item*t=&SR.a[i]; if(t->wid>=0){ if(dl[r]>0){ Big x; big_mulu(&x,&k,(uint64_t)dl[r]); big_add(&pool[t->v],&x); } else if(dl[r]<0){ Big x; big_mulu(&x,&k,(uint64_t)(-dl[r])); big_sub(&pool[t->v],&x); } r++; } }
                // steps: k*(Dlast+bb) + bb*k(k-1)/2
                Big Dn=Dlast; if(bb>=0) big_addu(&Dn,(uint64_t)bb); else big_subu(&Dn,(uint64_t)(-bb));
                Big t1; big_mul(&t1,&k,&Dn); 
                Big km1=k; big_subu(&km1,1); Big t2; big_mul(&t2,&k,&km1); Big t3; big_divu(&t3,&t2,2); Big t4; big_mulu(&t4,&t3,(uint64_t)(bb>=0?bb:-bb));
                big_add(&steps,&t1); if(bb>=0) big_add(&steps,&t4); else big_sub(&steps,&t4);
                Big e2; big_mulu(&e2,&k,(uint64_t)PERIOD); big_add(&ev,&e2);
                cyc++; nh=0; PL.active=PR.active=0;
                if(TARGET&&big_isu(&ev)&&big_u(&ev)==TARGET){ printf("event %llu steps ",(unsigned long long)TARGET); big_print(&steps); printf(" cyclejumps %ld shiftjumps %ld raw %llu\n",cyc,jumps,(unsigned long long)raw); return 0; }
                if(verb){ printf("J "); big_print(&k); printf(" cycles to event "); big_print(&ev); printf(" steps "); big_print(&steps); printf("\n"); }
                else if((cyc&(cyc-1))==0||cyc%1000==0){ printf("cycle jump %ld: event has %d digits, steps %d digits, items %ld, shift jumps %ld, raw %llu\n",cyc,big_digits(&ev),big_digits(&steps),SR.n,jumps,(unsigned long long)raw); fflush(stdout); }
                if(cyc>=maxj){ printf("stopped after %ld cycle jumps: event ",cyc); big_print(&ev); printf("\nsteps "); big_print(&steps); printf("\n"); g_s=s; g_cur=cur; if(getenv("DUMP")){ FILE*f=fopen(getenv("DUMP"),"w"); dump(f); fclose(f);} return 0; }
              } } }
        }
      }
    }
    if(PL.active&&pos>PL.reach) PL.reach=pos;
    if(PR.active&&pos<PR.reach) PR.reach=pos;
    (void)rawtotal;
  }
}
