// Exact Turing machine simulator with runs of words and context-carrying shift rules found on the fly.
//
// The tape is two stacks of items around the head cell; an item is one cell or a run (word, count).
// When the head arrives at a run (about to step onto the nearest cell of its nearest word) the simulator notes the
// state and starts a "probe". It then simulates that one word cell by cell. If the head next arrives at the following
// word of the same run in the same state, having read at most b cells behind it, and those b cells are again what
// they were at the start of the probe, then every further word of the run is crossed in exactly the same way (the
// head sees the same b cells behind and the same word ahead, and reads nothing else), so all remaining m words are
// crossed at once: m copies of the word left behind are deposited as a run and m*(steps of one crossing) are added.
// Runs are created when explicit cells repeat with one of the given periods, and extended when a full word is
// pushed next to a run of that word.
//
// The same holds when the state comes back only after j words (j <= JMAX): then the words are crossed j at a time.
//
// usage: accsim MACHINE EVENTS accel periods...     (accel=0: a plain simulator; the outputs must agree)
//   e.g.  accsim 1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF 1000000 1 3 11
// An event is the head reaching a new leftmost cell (LEFT=1, the default) or a new rightmost cell (-DLEFT=0).
// Output: at powers of two of events, the exact step count; a halt is reported with its step count.
// Environment: TRACE=start:every prints the tape every `every` events from event `start`; DUMP=file writes the
// final tape.  Nothing here is specific to one machine.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128;
#ifndef LEFT
#define LEFT 1
#endif
static void pr128(u128 x){char b[50];int i=49;b[i]=0;if(!x)b[--i]='0';while(x){b[--i]='0'+(int)(x%10);x/=10;}fputs(b+i,stdout);}
#define MAXW 4096
#define WL 48
#define K 40
#define JMAX 4
static unsigned char words[MAXW][WL]; static int wlen[MAXW]; static int nwords=0;
static int word_id(const unsigned char*c,int L){ for(int i=0;i<nwords;i++) if(wlen[i]==L&&!memcmp(words[i],c,L)) return i;
  if(nwords>=MAXW){fprintf(stderr,"too many words\n");exit(1);} memcpy(words[nwords],c,L); wlen[nwords]=L; return nwords++; }
typedef struct { int32_t wid; int64_t cnt; } Item;   // wid<0: one cell, value cnt
typedef struct { Item*a; long n,cap; long ex; int dir; long thr; } Stack; // ex: explicit cells on top; dir 0: left stack (top = rightmost), 1: right stack
static Stack SL,SR;
static int nper; static int pers[8]; static int ACC=1;
static void grow(Stack*s){ if(s->n+WL+4>=s->cap){ s->cap*=2; s->a=realloc(s->a,s->cap*sizeof(Item)); if(!s->a){fprintf(stderr,"memory\n");exit(1);} } }
static inline void raw_push(Stack*s,int c){ grow(s); s->a[s->n].wid=-1; s->a[s->n].cnt=c; s->n++; s->ex++; }
static void push_run(Stack*s,int wid,int64_t cnt){ grow(s); if(s->n>0&&s->a[s->n-1].wid==wid){ s->a[s->n-1].cnt+=cnt; } else { s->a[s->n].wid=wid; s->a[s->n].cnt=cnt; s->n++; } s->ex=0; }
// the word of a run as stored in tape order; cells of the top-of-stack side come first in "stack order"
static inline int word_cell(const Stack*s,int wid,int k){ // k-th cell from the top of the stack inside one word
  return s->dir==0 ? words[wid][wlen[wid]-1-k] : words[wid][k]; }
static void compress(Stack*s){ // called after an explicit push
  if(!ACC) return;
  for(int pi=0;pi<nper;pi++){ int L=pers[pi];
    if(s->ex==L && s->n>L && s->a[s->n-L-1].wid>=0 && wlen[s->a[s->n-L-1].wid]==L){ // a full word on a run of the same word?
      int wid=s->a[s->n-L-1].wid; int ok=1; for(int k=0;k<L&&ok;k++) if((int)s->a[s->n-1-k].cnt!=word_cell(s,wid,k)) ok=0;
      if(ok){ s->n-=L; s->a[s->n-1].cnt++; s->ex=0; return; } }
    int need=(L<8?4:2)*L;
    if(s->ex>=need){ int ok=1; for(int k=0;k<need-L&&ok;k++) if(s->a[s->n-1-k].cnt!=s->a[s->n-1-k-L].cnt) ok=0;
      if(ok){ unsigned char c[WL]; for(int k=0;k<L;k++){ int v=(int)s->a[s->n-1-k].cnt; if(s->dir==0) c[L-1-k]=v; else c[k]=v; }
        int wid=word_id(c,L); s->n-=need; s->ex-=need; long keep=s->ex; push_run(s,wid,need/L); s->ex=0; (void)keep; return; } }
  }
}
#define KEEP 24
static unsigned char sbuf[1<<20];
static void sweep(Stack*s){ // re-code the explicit cells below the KEEP cells nearest the head: periodic stretches become runs
  long m=0; while(s->n>0&&s->a[s->n-1].wid<0&&m<(long)sizeof(sbuf)){ sbuf[m++]=(unsigned char)s->a[s->n-1].cnt; s->n--; }   // sbuf[0] nearest the head
  long i=m-1; s->ex=0;                                                            // push back from the deepest
  while(i>=KEEP){ int done=0;
    for(int pi=0;pi<nper&&!done;pi++){ int L=pers[pi]; int minr=(L<8?4:2); long r=1; 
      if(i-KEEP+1<(long)minr*L) continue;
      while(i-(r+1)*L+1>=KEEP){ int ok=1; for(int k=0;k<L&&ok;k++) if(sbuf[i-k]!=sbuf[i-r*L-k]) ok=0; if(!ok)break; r++; }
      if(r>=minr){ unsigned char c[WL]; for(int k=0;k<L;k++){ if(s->dir==0) c[k]=sbuf[i-k]; else c[L-1-k]=sbuf[i-k]; }
        push_run(s,word_id(c,L),r); i-=r*L; done=1; } }
    if(!done){ raw_push(s,sbuf[i]); i--; } }
  while(i>=0){ raw_push(s,sbuf[i]); i--; }
}
static inline void push(Stack*s,int c){ raw_push(s,c); if(s->ex>=3) compress(s); if(ACC&&++s->thr>=2048){ sweep(s); s->thr=0; } }
static void expand(Stack*s){ // top item is a run: take one word off it and push its cells
  Item*t=&s->a[s->n-1]; int wid=t->wid; int L=wlen[wid]; if(--t->cnt==0) s->n--;
  grow(s); for(int k=L-1;k>=0;k--){ s->a[s->n].wid=-1; s->a[s->n].cnt=word_cell(s,wid,k); s->n++; } s->ex=L; }
static inline int raw_pop(Stack*s){ if(s->n==0) return 0; if(s->a[s->n-1].wid>=0) expand(s); s->n--; if(s->ex>0)s->ex--; return (int)s->a[s->n].cnt; }
static int peek(const Stack*s,int k,unsigned char*out){ // the k cells nearest the head; returns how many exist explicitly or in runs (blank beyond)
  long i=s->n-1; int got=0; while(got<k){ if(i<0){ out[got++]=0; continue; } const Item*t=&s->a[i];
    if(t->wid<0){ out[got++]=(unsigned char)t->cnt; i--; } else { int L=wlen[t->wid]; int64_t c=t->cnt; int64_t j=0; while(got<k&&j<c*L){ out[got++]=word_cell(s,t->wid,(int)(j%L)); j++; } i--; } }
  return got; }
typedef struct { int active; long q; long height; int wid; int st; unsigned char ctx[K]; long reach; u128 steps0; } Probe;
static Probe PL,PR;
static int g_s,g_cur;
static void dump(FILE*f){ for(int side=0;side<2;side++){ Stack*st=side?&SR:&SL; if(side) fprintf(f," [%c>%d] ",'A'+g_s,g_cur);
      for(long i=side?st->n-1:0; side? i>=0 : i<st->n; i+=side?-1:1){ Item*t=&st->a[i]; if(t->wid<0) fputc('0'+(int)t->cnt,f); else { fputc('(',f); for(int k=0;k<wlen[t->wid];k++)fputc('0'+words[t->wid][k],f); fprintf(f,")^%ld ",(long)t->cnt);} } } fputc('\n',f); }
int main(int argc,char**argv){
  const char*m=argv[1]; long maxev=atol(argv[2]); ACC=atoi(argv[3]); nper=0; for(int i=4;i<argc&&nper<8;i++) pers[nper++]=atoi(argv[i]);
  int W[6][2],D[6][2],S[6][2];
  for(int i=0;i<6;i++)for(int b=0;b<2;b++){const char*p=m+7*i+3*b; if(p[0]=='-'){S[i][b]=-1;continue;} W[i][b]=p[0]-'0';D[i][b]=(p[1]=='R')?1:-1;S[i][b]=p[2]-'A';}
  SL.cap=SR.cap=1<<16; SL.a=malloc(SL.cap*sizeof(Item)); SR.a=malloc(SR.cap*sizeof(Item)); SL.dir=0; SR.dir=1; SL.thr=SR.thr=0;
  long tr_start=0,tr_every=0; if(getenv("TRACE")) sscanf(getenv("TRACE"),"%ld:%ld",&tr_start,&tr_every);
  int cur=0,s=0; long pos=0,ext=0; u128 steps=0; long ev=0,nextp=1; long jumps=0; long raw=0;
  for(;;){
    if(S[s][cur]<0){ printf("HALT in state %c reading %d after ",'A'+s,cur); pr128(steps+1); printf(" steps (the halting step counted), event %ld, pos %ld\n",ev,pos); break; }
    int w=W[s][cur], d=D[s][cur]; s=S[s][cur]; steps++; raw++;
    if(d>0){
      push(&SL,w); pos++;
      if(SR.n>0&&SR.a[SR.n-1].wid>=0&&ACC){ // arriving at a run on the right
        Item*t=&SR.a[SR.n-1]; int L=wlen[t->wid]; int keep=0;
        if(PR.active&&PR.height==SR.n&&PR.wid==t->wid&&pos>PR.q&&(pos-PR.q)%L==0&&(pos-PR.q)/L<=JMAX){
          int jj=(int)((pos-PR.q)/L);
          if(PR.st!=s){ if(jj<JMAX) keep=1; }
          else { int b=(int)(PR.q-PR.reach); unsigned char c[K];
            if(b<=K-1&&jj*L<=WL){ peek(&SL,b,c); int ok=1; // the b cells behind must be what they were
              for(int k=0;k<b&&ok;k++) if(c[k]!=PR.ctx[k]) ok=0;
              int64_t mm=t->cnt/jj;
              if(ok&&mm>=1){ u128 delta=steps-PR.steps0; unsigned char cx[K],dd[WL]; int LL=jj*L;
                for(int k=0;k<b;k++) cx[k]=raw_pop(&SL);
                for(int k=0;k<LL;k++) dd[LL-1-k]=raw_pop(&SL);
                push_run(&SL,word_id(dd,LL),mm+1);
                for(int k=b-1;k>=0;k--) raw_push(&SL,cx[k]);
                t=&SR.a[SR.n-1]; t->cnt-=mm*jj; if(t->cnt==0){ SR.n--; } SR.ex=0;
                steps+=(u128)mm*delta; pos+=mm*LL; jumps++; } } }
        }
        if(!keep){ PR.active=0;
          if(SR.n>0&&SR.a[SR.n-1].wid>=0){ PR.active=1; PR.q=pos; PR.wid=SR.a[SR.n-1].wid; PR.st=s; PR.reach=pos; PR.steps0=steps; peek(&SL,K,PR.ctx);
            PR.height=SR.n; } }
        if(PR.active&&SR.n>0&&SR.a[SR.n-1].wid>=0&&SR.a[SR.n-1].cnt==1) PR.height=-1; /* the run ends with this word: no further arrival at it */
      }
      cur=raw_pop(&SR);
    } else {
      push(&SR,w); pos--;
      if(SL.n>0&&SL.a[SL.n-1].wid>=0&&ACC){ // arriving at a run on the left
        Item*t=&SL.a[SL.n-1]; int L=wlen[t->wid]; int keep=0;
        if(PL.active&&PL.height==SL.n&&PL.wid==t->wid&&pos<PL.q&&(PL.q-pos)%L==0&&(PL.q-pos)/L<=JMAX){
          int jj=(int)((PL.q-pos)/L);
          if(PL.st!=s){ if(jj<JMAX) keep=1; }
          else { int b=(int)(PL.reach-PL.q); unsigned char c[K];
            if(b<=K-1&&jj*L<=WL){ peek(&SR,b,c); int ok=1;
              for(int k=0;k<b&&ok;k++) if(c[k]!=PL.ctx[k]) ok=0;
              int64_t mm=t->cnt/jj;
              if(ok&&mm>=1){ u128 delta=steps-PL.steps0; unsigned char cx[K],dd[WL]; int LL=jj*L;
                for(int k=0;k<b;k++) cx[k]=raw_pop(&SR);
                for(int k=0;k<LL;k++) dd[k]=raw_pop(&SR);
                push_run(&SR,word_id(dd,LL),mm+1);
                for(int k=b-1;k>=0;k--) raw_push(&SR,cx[k]);
                t=&SL.a[SL.n-1]; t->cnt-=mm*jj; if(t->cnt==0){ SL.n--; } SL.ex=0;
                steps+=(u128)mm*delta; pos-=mm*LL; jumps++; } } }
        }
        if(!keep){ PL.active=0;
          if(SL.n>0&&SL.a[SL.n-1].wid>=0){ PL.active=1; PL.q=pos; PL.wid=SL.a[SL.n-1].wid; PL.st=s; PL.reach=pos; PL.steps0=steps; peek(&SR,K,PL.ctx);
            PL.height=SL.n; } }
        if(PL.active&&SL.n>0&&SL.a[SL.n-1].wid>=0&&SL.a[SL.n-1].cnt==1) PL.height=-1;
      }
      cur=raw_pop(&SL);
    }
    if(PL.active&&pos>PL.reach) PL.reach=pos;
    if(PR.active&&pos<PR.reach) PR.reach=pos;
    if(LEFT? pos<ext : pos>ext){ ext=pos; ev++;
      if(ev==nextp||ev==maxev){ printf("event %ld steps ",ev); pr128(steps); printf(" state %c pos %ld items %ld+%ld words %d jumps %ld raw %ld\n",'A'+s,pos,SL.n,SR.n,nwords,jumps,raw); fflush(stdout); if(ev==nextp)nextp*=2; }
      if(tr_every&&ev>=tr_start&&(ev-tr_start)%tr_every==0){ printf("T %ld ",ev); pr128(steps); printf(" "); g_s=s; g_cur=cur; dump(stdout); }
      if(ev>=maxev) break; }
  }
  if(getenv("DUMP")){ FILE*f=fopen(getenv("DUMP"),"w"); g_s=s; g_cur=cur; dump(f); fclose(f); }
  return 0;
}
