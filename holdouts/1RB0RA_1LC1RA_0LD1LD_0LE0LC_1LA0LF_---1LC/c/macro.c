/* 1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC: a run-length simulator with phase jumps.

   The tape is two stacks of runs (nearest the head last): Z n = 0^n, O n = 1^n, T n = (10)^n (read left to right).
   The head sits between the stacks and faces the stack it reads next (the direction of its last move).
   Moves: single machine steps, the six shift rules of the machine
       A> 1^n -> 0^n A>          A> 0 (10)^n -> 1^2n A> 0        B> (10)^n -> 1^2n B>
       1^2n <C -> <C (01)^n      (10)^n <C -> <C 0^2n            1^2n <D -> <D (10)^n
   and the phase jump (Lean: cycle_gap, phase_gap in lean/Gap.lean): with at least 6k zeros left of the head cell,
       0^6k A>0 (10)^x 00 (10)^y 110 0 1^w 0  ->  A>0 (10)^(x+3k) 00 (10)^(y-k) 110 0 1^(w+2k) 0     (k <= y)
   in k(8x+4y+26) + 10k(k-1) steps, and the same phase against a wall of 1s (the head on the last 1):
       1^2k <A (10)^x 00 (10)^y 110 0 1^w 0  ->  <A (10)^(x+k) 00 (10)^(y-k) 110 0 1^(w+2k) 0      (k <= y, x >= 1)
   in k(8x+4y+18) + 2k(k-1) steps.
   usage: macro LOG10_STEPS|=STEPS [nojump] [bits|runs]
   Runs until at least that many steps are done (a macro move is not cut), prints a line at each main phase start
   (the tape `A>0 10 00 (10)^y ...` at the left end: step, y, cells and ones right of the head, a fingerprint of
   the tape) and the final count; `nojump` turns the phase jumps off, `bits`/`runs` print the final tape.
   Steps are 128-bit and counts 64-bit: good to about 5e36 steps.
   Exactness is tested against the plain simulator by py/test_macro.py. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef __int128 i128; typedef long long i64;
typedef struct { char t; i64 n; } Run;
#define CAP (1<<25)   /* runs per stack (untouched pages cost nothing) */
static Run Ls[CAP], Rs[CAP]; static long ln=0, rn=0;   /* empty stack = blank tape */
static i128 steps=0; static i64 msteps=0, jumps=0; static int st=0, face=1;
static void die(const char*s){ fprintf(stderr,"%s\n",s); exit(2); }
static void pushrun(Run*S,long*n,char t,i64 c){ if(c<=0) return;
  if(c>(i64)2000000000000000000LL) die("count overflow (the limit of this program is about 5e36 steps)");
  if(*n==0 && t=='Z') return;
  if(*n>0 && S[*n-1].t==t){ S[*n-1].n+=c; return; }
  if(*n>=CAP-4) die("stack overflow");
  S[*n].t=t; S[*n].n=c; (*n)++; }
/* right stack: T n reads 1 0 1 0 ... from the head outwards; left stack: T n reads ... 1 0 with the 0 nearest */
static int popbit(Run*S,long*n,int right){ if(*n==0) return 0;
  Run*r=&S[*n-1]; char t=r->t; r->n--; if(r->n==0) (*n)--;
  if(t=='Z') return 0;
  if(t=='O') return 1;
  if(right){ pushrun(S,n,'Z',1); return 1; } else { pushrun(S,n,'O',1); return 0; } }
static void pushbit(Run*S,long*n,int right,int b){
  if(right){ if(b==0){ pushrun(S,n,'Z',1); return; }
    if(*n>0 && S[*n-1].t=='Z'){ if(--S[*n-1].n==0) (*n)--; pushrun(S,n,'T',1); return; }
    pushrun(S,n,'O',1); }
  else { if(b==1){ pushrun(S,n,'O',1); return; }
    if(*n>0 && S[*n-1].t=='O'){ if(--S[*n-1].n==0) (*n)--; pushrun(S,n,'T',1); return; }
    pushrun(S,n,'Z',1); } }
static const int W[6][2]={{1,0},{1,1},{0,1},{0,0},{1,0},{-1,1}}, D[6][2]={{1,1},{-1,1},{-1,-1},{-1,-1},{-1,-1},{0,-1}},
  S[6][2]={{1,0},{2,0},{3,3},{4,2},{0,5},{-1,2}};
static int halted=0, nojump=0;
static i64 mainy=-1;

/* normal form of the top `m` runs of the right stack: maximal (10)-runs, no T 1 */
static Run nb[64]; static int nbn;
static void emit(char t,i64 c){ if(c<=0) return;
  if(t=='Z' && nbn>0 && nb[nbn-1].t=='O'){ if(--nb[nbn-1].n==0) nbn--;
     if(nbn>0 && nb[nbn-1].t=='T') nb[nbn-1].n++; else { nb[nbn].t='T'; nb[nbn].n=1; nbn++; }
     c--; if(c>0){ nb[nbn].t='Z'; nb[nbn].n=c; nbn++; } return; }
  if(nbn>0 && nb[nbn-1].t==t){ nb[nbn-1].n+=c; return; }
  nb[nbn].t=t; nb[nbn].n=c; nbn++; }
static int normtop(int m){ /* returns the number of runs taken; nb[0..nbn) is the normal form, head side first */
  int k = rn<m ? (int)rn : m; nbn=0;
  for(int i=0;i<k;i++){ Run r=Rs[rn-1-i]; if(r.t=='T' && r.n==1){ emit('O',1); emit('Z',1);} else emit(r.t,r.n); }
  Run tmp[64]; int tn=0;
  for(int i=0;i<nbn;i++){ Run r=nb[i];
    if(r.t=='T' && r.n==1){ if(tn>0 && tmp[tn-1].t=='O') tmp[tn-1].n++; else { tmp[tn].t='O'; tmp[tn].n=1; tn++; }
       tmp[tn].t='Z'; tmp[tn].n=1; tn++; }
    else if(tn>0 && tmp[tn-1].t==r.t) tmp[tn-1].n+=r.n; else tmp[tn++]=r; }
  memcpy(nb,tmp,sizeof(Run)*tn); nbn=tn; return k; }
static void putback(int k){ rn-=k; for(int i=nbn-1;i>=0;i--) if(nb[i].n>0){ Rs[rn++]=nb[i]; } }

static int tryjump(void){ /* A facing left onto a 0, right top T x */
  i64 g; int ones=0;                 /* g: cycles the left side allows (-1: any number) */
  if(ln==0) g=-1; else if(Ls[ln-1].t=='Z') g=(Ls[ln-1].n-1)/6; else if(Ls[ln-1].t=='O'){ g=Ls[ln-1].n/2; ones=1; } else return 0;
  if(g==0) return 0;
  int k0=normtop(12); int ok=0; i64 k=0;
  /* T^x Z2 T^y O2 Z2 O^w ... (the 1s of w, whatever follows) or O2 Z2 with no O run after it */
  if(nbn>=5 && nb[0].t=='T' && nb[1].t=='Z'&&nb[1].n==2 && nb[2].t=='T'
     && nb[3].t=='O'&&nb[3].n==2 && nb[4].t=='Z'&&nb[4].n>=2){
    i64 x=nb[0].n, y=nb[2].n; int wform = (nb[4].n==2 && nbn>=6 && nb[5].t=='O') ? 1 : 2;   /* 2: w = 0, or w = 1 inside a following T run */
    if(wform){ k=y; if(g>=0 && g<k) k=g;
      if(k>0){ ok=1;
        if(ones){ steps += (i128)k*(8*(i128)x+4*(i128)y+18) + (i128)2*k*(k-1); nb[0].n=x+k; }
        else { steps += (i128)k*(8*(i128)x+4*(i128)y+26) + (i128)10*k*(k-1); nb[0].n=x+3*k; }
        nb[2].n=y-k;
        if(wform==1) nb[5].n+=2*k;
        else { /* O2 Z c  ->  O2 Z2 O^2k Z^(c-2) */
          i64 c=nb[4].n; for(int i=nbn-1;i>4;i--) nb[i+2]=nb[i]; nbn+=2;
          nb[4].n=2; nb[5].t='O'; nb[5].n=2*k; nb[6].t='Z'; nb[6].n=c-2; }
        if(g>=0){ Ls[ln-1].n-=(ones?2:6)*k; if(Ls[ln-1].n==0) ln--; }
        jumps++; } } }
  putback(k0); return ok; }

/* a fingerprint of the tape right of the head: sum of i and of i^2 over the cells i = 0, 1, ... that hold a 1, mod 2^61-1 */
typedef unsigned __int128 u128; typedef unsigned long long u64;
#define MP ((u64)2305843009213693951ULL)
static u64 mm(u64 a,u64 b){ return (u64)((u128)a*b%MP); }
static void fingerprint(u64*h1,u64*h2,i128*ones,i128*len){
  u64 s1=0,s2=0, inv2=(MP+1)/2, inv6=mm(inv2,(2*MP+1)/3); i128 a=0, o=0;
  for(long i=rn-1;i>=0;i--){ u64 n=(u64)(Rs[i].n%MP), am=(u64)(a%MP); i64 c=Rs[i].n;
    u64 t1=mm(mm(n,(n+MP-1)%MP),inv2), t2=mm(mm(mm((n+MP-1)%MP,n),(2*n+MP-1)%MP),inv6);   /* sum j, sum j^2, j<n */
    if(Rs[i].t=='O'){ s1=(s1+mm(n,am)+t1)%MP; s2=(s2+mm(n,mm(am,am))+mm(2*am%MP,t1)+t2)%MP; o+=c; a+=c; }
    else if(Rs[i].t=='T'){ s1=(s1+mm(n,am)+2*t1)%MP; s2=(s2+mm(n,mm(am,am))+mm(4*am%MP,t1)+4*t2)%MP; o+=c; a+=2*(i128)c; }
    else a+=c; }
  *h1=s1; *h2=s2; *ones=o; *len=a; }
static char*dec(i128 s){ static char buf[8][64]; static int w=0; char*b=buf[w=(w+1)%8]; int bi=63; b[63]=0;
  if(s==0) b[--bi]='0';
  while(s>0){ b[--bi]='0'+(int)(s%10); s/=10; }
  return b+bi; }
static void report_main(void){ /* at the left end, A facing left: is the tape 0 10 00 (10)^y ? */
  int k0=normtop(6); i64 y=-1;
  if(nbn>=3 && nb[0].t=='O'&&nb[0].n==1 && nb[1].t=='Z'&&nb[1].n==3 && nb[2].t=='T') y=nb[2].n;
  putback(k0);
  if(y>=0 && y!=mainy){ mainy=y; u64 h1,h2; i128 o,l; fingerprint(&h1,&h2,&o,&l);
    printf("main phase: step %s y %lld cells %s ones %s fp %llu %llu runs %ld msteps %lld jumps %lld\n",
           dec(steps),y,dec(l),dec(o),h1,h2,rn,msteps,jumps); fflush(stdout); } }

static void step(void){ msteps++;
  if(face==1){
    if(st==0){
      if(rn>0 && Rs[rn-1].t=='O'){ i64 n=Rs[rn-1].n; rn--; pushrun(Ls,&ln,'Z',n); steps+=n; return; }
      if(rn>1 && Rs[rn-1].t=='Z' && Rs[rn-1].n==1 && Rs[rn-2].t=='T'){
        i64 n=Rs[rn-2].n; Rs[rn-2]=Rs[rn-1]; rn--; pushrun(Ls,&ln,'O',2*n); steps+=2*n; return; }
    } else if(st==1){
      if(rn>0 && Rs[rn-1].t=='T'){ i64 n=Rs[rn-1].n; rn--; pushrun(Ls,&ln,'O',2*n); steps+=2*n; return; } }
  } else {
    if(st==0 && (ln==0 || Ls[ln-1].t!='T')){
      if(ln==0) report_main();
      if(!nojump && rn>0 && tryjump()) return; }
    if(st==2 && ln>0){
      if(Ls[ln-1].t=='O' && Ls[ln-1].n>=2){ i64 n=Ls[ln-1].n/2; Ls[ln-1].n-=2*n; if(Ls[ln-1].n==0) ln--;
        pushbit(Rs,&rn,1,1); pushrun(Rs,&rn,'T',n-1); pushbit(Rs,&rn,1,0); steps+=2*n; return; }
      if(Ls[ln-1].t=='T'){ i64 n=Ls[ln-1].n; ln--; pushrun(Rs,&rn,'Z',2*n); steps+=2*n; return; }
    } else if(st==3 && ln>0){
      if(Ls[ln-1].t=='O' && Ls[ln-1].n>=2){ i64 n=Ls[ln-1].n/2; Ls[ln-1].n-=2*n; if(Ls[ln-1].n==0) ln--;
        pushrun(Rs,&rn,'T',n); steps+=2*n; return; } } }
  {
  int b = face==1 ? popbit(Rs,&rn,1) : popbit(Ls,&ln,0);
  if(S[st][b]<0){ halted=1; steps++; return; }
  int w=W[st][b], d=D[st][b]; st=S[st][b]; steps++;
  if(d==1){ pushbit(Ls,&ln,0,w); face=1; } else { pushbit(Rs,&rn,1,w); face=-1; } } }

static void printbits(void){ /* whole tape, left to right, with the head */
  for(long i=0;i<ln;i++){ Run r=Ls[i]; for(i64 j=0;j<r.n;j++) fputs(r.t=='Z'?"0":r.t=='O'?"1":"10",stdout); }
  printf(face==1?" %c> ":" <%c ","ABCDEF"[st]);
  for(long i=rn-1;i>=0;i--){ Run r=Rs[i]; for(i64 j=0;j<r.n;j++) fputs(r.t=='Z'?"0":r.t=='O'?"1":"10",stdout); }
  putchar('\n'); }
static void printruns(void){
  for(long i=0;i<ln;i++) printf("%c%lld ",Ls[i].t,Ls[i].n);
  printf(face==1?"%c> ":"<%c ","ABCDEF"[st]);
  for(long i=rn-1;i>=0;i--) printf("%c%lld ",Rs[i].t,Rs[i].n);
  putchar('\n'); }

int main(int c,char**v){ if(c<2){ fprintf(stderr,"usage: macro LOG10_STEPS|=STEPS [nojump] [bits|runs]\n"); return 1; }
  i128 max=1; if(v[1][0]=='='){ max=0; for(char*p=v[1]+1;*p;p++) max=max*10+(*p-'0'); }
  else { double e=atof(v[1]); int ie=(int)e; for(int i=0;i<ie;i++) max*=10; }
  int bits=0, runs=0; for(int i=2;i<c;i++){ if(!strcmp(v[i],"nojump")) nojump=1; if(!strcmp(v[i],"bits")) bits=1; if(!strcmp(v[i],"runs")) runs=1; }
  while(steps<max && !halted) step();
  printf("%s %s steps, %lld macro steps, %lld jumps, runs L %ld R %ld\n", halted?"HALT at":"no halt in", dec(steps), msteps, jumps, ln, rn);
  if(bits) printbits();
  if(runs) printruns();
  return 0; }
