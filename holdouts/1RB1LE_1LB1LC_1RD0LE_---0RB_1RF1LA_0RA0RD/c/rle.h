/* rle.h: exact simulation of a two-symbol machine on a run-length coded tape, with two accelerations that are
 * exact by construction:
 *   sweep: the head, in state s, reads x, and every transition of the chain s -> s' -> ... on x writes x and moves
 *          the same way: crossing a run x^L takes L steps and ends in chain[L mod period];
 *   slide: the head reads a in state s with a run x^k beyond it, and a one-copy simulation on the window
 *          [a x x] shows the head returning to state s one cell further with the window [x a x] after T steps,
 *          never reading past the window: then j copies take j*T steps (applied while 2 more x's remain).
 * Everything else is single steps.  Step counts follow bbchallenge (the halting transition counts).
 */
#ifndef RLE_H
#define RLE_H
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll;
typedef struct { int n; int w[10][2], d[10][2], s[10][2]; } mach;
static int parse_m(const char *t, mach *m){ int len=strlen(t); m->n=(len+1)/7;
  for(int s=0;s<m->n;s++) for(int y=0;y<2;y++){ const char*c=t+7*s+3*y;
    if(c[2]=='-'||c[2]-'A'<0||c[2]-'A'>=m->n){m->s[s][y]=-1;m->w[s][y]=0;m->d[s][y]=0;}
    else {m->w[s][y]=c[0]-'0'; m->d[s][y]=c[1]=='R'?1:-1; m->s[s][y]=c[2]-'A';}} return 0; }
typedef struct { int sym; ll len; } run;
typedef struct { run *a; ll n, cap; } stk;     /* top = a[n-1] is nearest the head; bottom: blank (implicit) */
static void push(stk *s, int sym, ll len){ if(len<=0) return; if(s->n && s->a[s->n-1].sym==sym){ s->a[s->n-1].len+=len; return; }
  if(s->n==s->cap){ s->cap=s->cap?2*s->cap:64; s->a=realloc(s->a,s->cap*sizeof(run)); } s->a[s->n].sym=sym; s->a[s->n].len=len; s->n++; }
static int topsym(stk *s){ return s->n? s->a[s->n-1].sym : 0; }
static ll toplen(stk *s){ return s->n? s->a[s->n-1].len : (ll)4e18; }
static void popn(stk *s, ll k){ if(!s->n) return; s->a[s->n-1].len-=k; if(s->a[s->n-1].len<=0) s->n--; }
/* run of index i from the top (0 = top): sym, len (blank beyond) */
static int symat(stk *s, ll i){ return i < s->n ? s->a[s->n-1-i].sym : 0; }
static ll lenat(stk *s, ll i){ return i < s->n ? s->a[s->n-1-i].len : (ll)4e18; }
typedef struct { mach m; stk L, R; int st; ll steps; int halted; ll pos; /* head position (cell index) */
  int chain[10][2][2][10], cper[10][2][2];      /* sweep chains: [state][sym][dir 0=L,1=R] */
  int slideT[10][2][2][2];                       /* [state][a][x][dir]: T or 0 */ } tm;
static void prep(tm *t){
  for(int s=0;s<t->m.n;s++) for(int x=0;x<2;x++) for(int dd=0;dd<2;dd++){
    int d=dd?1:-1, q=s, k=0; t->cper[s][x][dd]=0;
    int seen[10]; memset(seen,-1,sizeof seen);
    while(k<10){ if(t->m.s[q][x]<0||t->m.w[q][x]!=x||t->m.d[q][x]!=d) break;
      if(seen[q]>=0) break; seen[q]=k; t->chain[s][x][dd][k]=q; q=t->m.s[q][x]; k++; }
    if(k>0 && seen[q]==0) t->cper[s][x][dd]=k;   /* pure cycle back to s */
  }
  for(int s=0;s<t->m.n;s++) for(int a=0;a<2;a++) for(int x=0;x<2;x++) for(int dd=0;dd<2;dd++){
    t->slideT[s][a][x][dd]=0; if(a==x) continue;
    int d=dd?1:-1, c[3]={a,x,x}, h=0, q=s;
    for(int T=1;T<=60;T++){ if(t->m.s[q][c[h]]<0) break; int w=t->m.w[q][c[h]], dir=t->m.d[q][c[h]]*d, nq=t->m.s[q][c[h]];
      c[h]=w; h+=dir; q=nq; if(h<0||h>2) break;
      if(h==1 && q==s && c[0]==x && c[1]==a && c[2]==x){ t->slideT[s][a][x][dd]=T; break; } }
  }
}
static void init(tm *t, const char *M){ memset(t,0,sizeof *t); parse_m(M,&t->m); prep(t); }
/* one step; returns 0 on halt */
static int step1(tm *t){
  int x=topsym(&t->R), s=t->st;
  if(t->m.s[s][x]<0){ t->halted=1; t->steps++; return 0; }
  int w=t->m.w[s][x], d=t->m.d[s][x];
  popn(&t->R,1);
  if(d>0){ push(&t->L,w,1); } else { int y=topsym(&t->L); popn(&t->L,1); push(&t->R,w,1); push(&t->R,y,1); }
  t->st=t->m.s[s][x]; t->steps++; t->pos+=d; return 1;
}
/* one move: an accelerated jump if one applies, else a step */
static int move(tm *t){
  int s=t->st, x=topsym(&t->R);
  /* sweep left over x: head cell and the run of x on the left */
  for(int dd=0;dd<2;dd++){ int per=t->cper[s][x][dd]; if(!per) continue;
    if(dd==0){ /* moving left: cross head cell + left run of x */
      if(!t->L.n || topsym(&t->L)!=x) continue;
      ll k=toplen(&t->L)+1; popn(&t->R,1); popn(&t->L,k-1); push(&t->R,x,k); { int y=topsym(&t->L); popn(&t->L,1); push(&t->R,y,1); }
      t->st=t->chain[s][x][0][k%per]; t->steps+=k; t->pos-=k; return 1; }
    else { if(!t->R.n) continue; ll k=toplen(&t->R); if(k>=(ll)4e18) continue;
      popn(&t->R,k); push(&t->L,x,k); t->st=t->chain[s][x][1][k%per]; t->steps+=k; t->pos+=k; return 1; }
  }
  /* slide right: head cell a (a single cell of its run), run x^k next */
  if(t->R.n && lenat(&t->R,0)==1){ int y=symat(&t->R,1); int T=t->slideT[s][x][y][1];
    if(T && t->R.n>=2){ ll k=lenat(&t->R,1); ll j=k-2; if(j>0){ popn(&t->R,1); popn(&t->R,j); push(&t->L,y,j); push(&t->R,x,1);
        t->steps+=j*T; t->pos+=j; return 1; } } }
  /* slide left: head cell a, run x^k on the left (head cell is its run's first cell on the right stack, and the
     cell right of the head is not needed) */
  if(t->L.n){ int y=topsym(&t->L); int T=t->slideT[s][x][y][0];
    if(T){ ll k=toplen(&t->L); ll j=k-2; if(j>0 && t->L.n>=1){ popn(&t->R,1); popn(&t->L,j); push(&t->R,y,j); push(&t->R,x,1);
        t->steps+=j*T; t->pos-=j; return 1; } } }
  return step1(t);
}
static void print_tape(tm *t, FILE *f){
  for(ll i=0;i<t->L.n;i++){ run r=t->L.a[i]; fprintf(f, r.len>1?"%d^%lld ":"%d ", r.sym, r.len); }
  fprintf(f,"%c> ",'A'+t->st);
  for(ll i=t->R.n-1;i>=0;i--){ run r=t->R.a[i]; fprintf(f, r.len>1?"%d^%lld ":"%d ", r.sym, r.len); }
  fputc('\n',f);
}
#endif
