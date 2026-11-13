/* tok: an exact run-length simulator for any two-symbol machine (written for the G07 holdouts) with tokens (word of up to 8 cells, count) on two stacks, crossing a whole token run
   when one copy is crossed in the same state (the word may change, uniformly).  Words are folded from the cells the
   head leaves behind: a literal word equal to the token under it (or repeated twice) becomes a count.
   usage: tok MACHINE MAXSTEPS EVSTATE EVSIDE(L|R) EVERY [MAXEV]
   prints at every EVERY-th event (head at that end of the tape in EVSTATE): ev steps tape (tokens, left to right) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll; typedef unsigned __int128 u128;
int tw[8][2], td[8][2], ts[8][2], ns;
typedef struct { unsigned char w[8]; int len; u128 cnt; } Tok;
typedef struct { Tok *t; ll n, cap; } Stk;   /* top = t[n-1] is nearest the head; words are written in order
   from the head outward?  No: words stored in tape order (left to right) for both stacks. */
static void push(Stk*s, Tok x){ if(s->n==s->cap){ s->cap=s->cap?2*s->cap:1024; s->t=realloc(s->t,sizeof(Tok)*s->cap);} s->t[s->n++]=x; }
Stk L, R; /* L: tokens left of head, top nearest; R: tokens from head rightwards, top = token containing head cell */
int maxw=4;
void pr128(u128 x){ char b[64]; int i=63; b[i]=0; if(!x){putchar('0');return;} while(x){b[--i]='0'+(int)(x%10);x/=10;} fputs(b+i,stdout); }
static int sameword(Tok*a, unsigned char*w, int len){ return a->len==len && !memcmp(a->w,w,len); }
/* push one cell onto L (cell to the left of head after moving right) and fold */
/* expand the top tokens of s into cells in tape order: top j tokens; returns the cell count or -1 if over 8 */
static int expand(Stk*s, ll from, int j, int leftside, unsigned char*out){
  /* tokens s->t[from-1], s->t[from-2], ... s->t[from-j] (from-1 nearest head) */
  unsigned char buf[16]; int n=0;
  for(int i=0;i<j;i++){ Tok*t=&s->t[from-1-i]; if(from-1-i<1) return -1; if((u128)t->len*t->cnt>8) return -1;
    int c=(int)t->cnt; if(n+t->len*c>8) return -1;
    /* cells of this token in tape order */
    unsigned char cell[8]; int m=0; for(int r=0;r<c;r++) for(int q=0;q<t->len;q++) cell[m++]=t->w[q];
    if(leftside){ /* tokens nearer the head are further right: prepend deeper ones */ memmove(buf+m,buf,n); memcpy(buf,cell,m); }
    else { memcpy(buf+n,cell,m); }
    n+=m; }
  memcpy(out,buf,n); return n; }
static void fold(Stk*s, int leftside){
  for(int j=1;j<=8 && j<s->n;j++){
    unsigned char w[16]; int k=expand(s,s->n,j,leftside,w); if(k<0) break;
    if(k>maxw) break;
    if(j==1 && s->t[s->n-1].cnt==1 && s->t[s->n-1].len==k && j==1){ /* a single token: compare with below */ }
    /* below token equal to w */
    if(s->n-1-j>=1){ Tok*b=&s->t[s->n-1-j]; if(sameword(b,w,k) && !(j==1 && s->t[s->n-1].len==k && s->t[s->n-1].cnt==1 && 0)){
        if(!(j==1 && sameword(&s->t[s->n-1],w,k))) { b->cnt++; s->n-=j; fold(s,leftside); return; }
        else { b->cnt+=s->t[s->n-1].cnt; s->n--; fold(s,leftside); return; } } }
    /* the next tokens below expand to w too: make w^2 */
    for(int j2=1;j2<=8 && s->n-j-j2>=1;j2++){ unsigned char w2[16]; int k2=expand(s,s->n-j,j2,leftside,w2); if(k2<0||k2>k) break;
      if(k2==k){ if(!memcmp(w,w2,k) && (j+j2>2 || k>1 || 1)){ if(j==1&&j2==1&&s->t[s->n-1].len==k&&s->t[s->n-2].len==k){ /* two equal single tokens */ s->t[s->n-2].cnt+=s->t[s->n-1].cnt; s->n--; fold(s,leftside); return; }
          s->n-=j+j2; Tok x; memcpy(x.w,w,k); x.len=k; x.cnt=2; push(s,x); fold(s,leftside); return; } break; } }
  }
}
static void pushcell(Stk*s,int c,int leftside){ Tok x; x.w[0]=c; x.len=1; x.cnt=1; push(s,x); fold(s,leftside); }
/* expose the head cell: make the top of R a literal cell (R top token is the head's), splitting a token */
static void split(Stk*s, int leftside){
  Tok t=s->t[s->n-1]; s->n--;
  if(t.cnt>1){ t.cnt--; push(s,t); }
  /* push the cells of one copy as literals: for R (head at the leftmost cell), push so that top = first cell */
  if(leftside){ for(int i=0;i<t.len;i++){ Tok x; x.w[0]=t.w[i]; x.len=1; x.cnt=1; push(s,x);} }
  else { for(int i=t.len-1;i>=0;i--){ Tok x; x.w[0]=t.w[i]; x.len=1; x.cnt=1; push(s,x);} }
}

/* can one copy of word w (len n) be crossed from the left (d=1) or right (d=0) in state q, same state out? */
static ll cancross(int q,const unsigned char*w,int n,int d,unsigned char*out){ int c[8]; for(int i=0;i<n;i++) c[i]=w[i];
  int i=d?0:n-1,s=q; ll k=0; while(i>=0&&i<n&&k<200){ if(ts[s][c[i]]<0) return -1; int r=c[i]; c[i]=tw[s][r]; int dd=td[s][r]; s=ts[s][r]; i+=dd; k++; }
  if(s!=q || (d&&i<n) || (!d&&i>=0)) return -1; if(out) for(int j=0;j<n;j++) out[j]=c[j]; return k; }
/* rotate: replace the top token w^n (n>=3) of stack s by literals and a rotated run so that the head side
   starts with a literal cell, if the rotated word can be crossed in state q */
static int rotate(Stk*s,int leftside,int q){ Tok t=s->t[s->n-1]; if(t.cnt<3||t.len<2) return 0;
  unsigned char rw[8]; int n=t.len;
  if(!leftside){ /* R stack, head enters from the left; tape: w0 (w1..w_{n-1} w0)^(cnt-1) w1..w_{n-1}; the head side is w0 */
    for(int i=0;i<n;i++) rw[i]=t.w[(i+1)%n];
    if(cancross(q,rw,n,1,0)<0) return 0;
    s->n--; for(int i=n-1;i>=1;i--){ Tok x; x.w[0]=t.w[i]; x.len=1; x.cnt=1; push(s,x);} /* far side literals (deepest first) */
    Tok y; memcpy(y.w,rw,n); y.len=n; y.cnt=t.cnt-1; push(s,y); Tok z; z.w[0]=t.w[0]; z.len=1; z.cnt=1; push(s,z); return 1; }
  else { /* L stack, head enters from the right; tape: w0..w_{n-2} (w_{n-1} w0..w_{n-2})^(cnt-1) w_{n-1} */
    for(int i=0;i<n;i++) rw[i]=t.w[(i+n-1)%n];
    if(cancross(q,rw,n,0,0)<0) return 0;
    s->n--; for(int i=0;i<n-1;i++){ Tok x; x.w[0]=t.w[i]; x.len=1; x.cnt=1; push(s,x);} 
    Tok y; memcpy(y.w,rw,n); y.len=n; y.cnt=t.cnt-1; push(s,y); Tok z; z.w[0]=t.w[n-1]; z.len=1; z.cnt=1; push(s,z); return 1; }
}
int main(int argc,char**argv){
  const char*m=argv[1]; ns=(strlen(m)+1)/7;
  for(int s=0;s<ns;s++) for(int r=0;r<2;r++){ const char*t=m+7*s+3*r; if(t[2]=='-'){ts[s][r]=-1;continue;} tw[s][r]=t[0]-'0'; td[s][r]=t[1]=='R'?1:-1; ts[s][r]=t[2]-'A'; }
  double maxsteps=atof(argv[2]); int evs=argv[3][0]-'A'; int evR=argv[4][0]=='R'; ll every=atoll(argv[5]); ll maxev=argc>6?atoll(argv[6]):(1LL<<62);
  if(getenv("MAXW")) maxw=atoi(getenv("MAXW"));
  /* blank ends: L bottom and R bottom are 'blank' sentinels: a token with len 1 cell 0 and huge count */
  Tok bl; bl.w[0]=0; bl.len=1; bl.cnt=(u128)1<<100; push(&L,bl); push(&R,bl);
  int st=0; u128 steps=0; ll ev=0; ll rdepth=0, ldepth=0; /* distance (in tokens? no) */
  /* track ends: cells beyond the visited region: use the sentinel count: visited ends = sentinel touched */
  while((double)steps<maxsteps){
    Tok*h=&R.t[R.n-1];
    /* try a run cross to the right: head at the leftmost cell of token h moving right... we only cross when we
       enter a token from its edge in a direction; the direction is the last move: keep it */
    static int dir=1;
    if(h->cnt>1 && h->len>=1 && R.n>1){
      /* crossing rightwards: simulate one copy from its left edge */
      int c[8]; for(int i=0;i<h->len;i++) c[i]=h->w[i]; int i=0,s=st; ll n=0; int okc=0;
      while(i>=0&&i<h->len&&n<200){ if(ts[s][c[i]]<0) break; int r=c[i]; c[i]=tw[s][r]; int d=td[s][r]; s=ts[s][r]; i+=d; n++; }
      if(i>=h->len && s==st){ okc=1; }
      if(!okc && L.n>1 && L.t[L.n-1].len==1 && L.t[L.n-1].cnt==1 && h->len<=6){
        /* the carried cell: u w -> v u with the head ending past it */
        int c2[8]; c2[0]=L.t[L.n-1].w[0]; int n2=h->len+1; for(int j=0;j<h->len;j++) c2[j+1]=h->w[j];
        int i2=1,s2=st; ll k2=0; while(i2>=0&&i2<n2&&k2<200){ if(ts[s2][c2[i2]]<0) break; int r=c2[i2]; c2[i2]=tw[s2][r]; int d=td[s2][r]; s2=ts[s2][r]; i2+=d; k2++; }
        if(i2>=n2 && s2==st && c2[n2-1]==L.t[L.n-1].w[0]){
          Tok x=*h; for(int j=0;j<h->len;j++) x.w[j]=c2[j]; u128 k=h->cnt; R.n--; steps+=(u128)k2*k;
          Tok uu=L.t[L.n-1]; L.n--;
          if(L.n>1 && sameword(&L.t[L.n-1],x.w,x.len)) L.t[L.n-1].cnt+=k; else push(&L,x);
          push(&L,uu); continue; } }
      if(okc){ Tok x=*h; for(int j=0;j<x.len;j++) x.w[j]=c[j]; u128 k=h->cnt; R.n--; steps+=(u128)n*k;
        /* push onto L: merge with top if same word */
        if(L.n>0 && sameword(&L.t[L.n-1],x.w,x.len) && L.n>1) L.t[L.n-1].cnt+=k; else push(&L,x);
        continue; }
    }
    if(R.n>1 && h->cnt>=3 && h->len>=2) rotate(&R,0,st), h=&R.t[R.n-1];
    if(h->len>1 || h->cnt>1){ if(R.n==1 && h->cnt>1){ /* blank sentinel: expose one blank */ h->cnt--; Tok x; x.w[0]=0;x.len=1;x.cnt=1; push(&R,x); }
                               else split(&R,0); h=&R.t[R.n-1]; }
    int r=h->w[0];
    if(ts[st][r]<0){ printf("HALT steps "); pr128(steps+1); printf(" state %c\n",'A'+st); return 0; }
    int w=tw[st][r], d=td[st][r]; st=ts[st][r]; steps++;
    R.n--; /* remove head cell */
    if(d==1){ pushcell(&L,w,1);
      if(R.n==0){} }
    else { /* move left: written cell goes onto R, head moves to top of L */
      Tok x; x.w[0]=w; x.len=1; x.cnt=1; push(&R,x); fold(&R,0);
      /* bring one cell from L to R top (the head cell) */
      Tok*lt=&L.t[L.n-1];
      if(L.n==1){ lt->cnt--; Tok y; y.w[0]=0;y.len=1;y.cnt=1; push(&R,y); if(!evR && st==evs){ ev++; if(ev%every==0){ printf("%lld ",ev); pr128(steps); putchar(' '); goto print; } } goto cont; }
      /* try a run cross to the left: token lt crossed from its right edge */
      if(lt->cnt>1){ int c[8]; for(int i=0;i<lt->len;i++) c[i]=lt->w[i]; int i=lt->len-1,s=st; ll n=0;
        while(i>=0&&i<lt->len&&n<200){ if(ts[s][c[i]]<0) break; int rr=c[i]; c[i]=tw[s][rr]; int dd=td[s][rr]; s=ts[s][rr]; i+=dd; n++; }
        if(i<0 && s==st){ Tok y=*lt; for(int j=0;j<y.len;j++) y.w[j]=c[j]; u128 k=lt->cnt; L.n--; steps+=(u128)n*k;
          if(R.n>1 && sameword(&R.t[R.n-1],y.w,y.len)) R.t[R.n-1].cnt+=k; else push(&R,y);
          /* the head is now left of the run: move one cell from L */
          lt=&L.t[L.n-1];
          if(L.n==1){ lt->cnt--; Tok z; z.w[0]=0;z.len=1;z.cnt=1; push(&R,z); if(!evR && st==evs){ ev++; if(ev%every==0){ printf("%lld ",ev); pr128(steps); putchar(' '); goto print; } } goto cont; }
        } }
      if(L.n>1 && lt->cnt>=3 && lt->len>=2) rotate(&L,1,st);
      lt=&L.t[L.n-1];
      if(lt->len>1||lt->cnt>1) split(&L,1);
      lt=&L.t[L.n-1]; Tok y=*lt; L.n--; push(&R,y);
    }
    cont:
    if(evR && d==1 && R.n==1 && st==evs){ /* head at the blank just right of the tape?  event: head reads blank at right end */
      ev++; if(ev%every==0){ printf("%lld ",ev); pr128(steps); putchar(' '); goto print; } }
    if(ev>=maxev) break;
    continue;
    print:
    for(ll i=1;i<L.n;i++){ Tok*t=&L.t[i]; for(int j=0;j<t->len;j++) putchar('0'+t->w[j]); if(t->cnt>1){ putchar('^'); pr128(t->cnt);} putchar(' '); }
    printf("%c> ",'A'+st);
    for(ll i=R.n-1;i>=1;i--){ Tok*t=&R.t[i]; for(int j=0;j<t->len;j++) putchar('0'+t->w[j]); if(t->cnt>1){ putchar('^'); pr128(t->cnt);} putchar(' '); }
    putchar('\n'); fflush(stdout);
    if(ev>=maxev) break;
  }
  { u128 ones=0; for(ll i=1;i<L.n;i++){ int o=0; for(int j=0;j<L.t[i].len;j++) o+=L.t[i].w[j]; ones+=(u128)o*L.t[i].cnt; }
    for(ll i=1;i<R.n;i++){ int o=0; for(int j=0;j<R.t[i].len;j++) o+=R.t[i].w[j]; ones+=(u128)o*R.t[i].cnt; }
    printf("END "); pr128(steps); printf(" ones "); pr128(ones); printf(" state %c\n",'A'+st); }
  return 0; }
