/* rl.c: an exact run-length simulator with shift rules found automatically, for the marker-counter family
   (the method of tools/py/bbtools/symtm.py on concrete counts, in C).

   usage: rl MACHINE MAXSTEPS SIDE STATE PWORD EVERY [MAXSWEEPS [FSTATE [QUIETF]]]
     SIDE R|L: the side where the tape grows; a sweep end is the head stepping onto a fresh cell on that side in
     state STATE.  PWORD (0010, or 0100
     for the mirrored machines) is the background word: at each sweep end the tape is rewritten as runs of PWORD
     and single cells.  EVERY > 0 prints every EVERY-th sweep end as "S <steps> <tape>" (blocks as B<count>, the
     tape read so that it grows to the right in both orientations); EVERY = 0 prints only the sweep ends where the
     number of tokens or the first block changes (with the sweep end before), and every entry into FSTATE
     (default F) as "F <steps> <symbol read>" (with QUIETF=1 only those that read a 1).
   Steps follow bbchallenge (the halting transition counts).  The step counter is 128-bit.
   Checked against a direct simulation by py/check_rl.py.
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned __int128 u128;
typedef struct { uint32_t w; uint8_t len; uint64_t c; } tok; /* w: bits, first cell = bit (len-1) ... cell i = (w>>(len-1-i))&1 */
#define CELL(t,i) (((t).w>>((t).len-1-(i)))&1)
typedef struct { tok *a; long n, cap; } stack;
static void push_raw(stack *s, tok t){ if(s->n==s->cap){s->cap=s->cap?2*s->cap:1024; s->a=realloc(s->a,s->cap*sizeof(tok));} s->a[s->n++]=t; }
static void push(stack *s, tok t){ if(t.c==0) return; if(s->n && s->a[s->n-1].len==t.len && s->a[s->n-1].w==t.w && t.len>1){ s->a[s->n-1].c+=t.c; return;} push_raw(s,t); }
static tok lit(int b){ tok t={ (uint32_t)b,1,1}; return t; }
int nst; int W[8][2], D[8][2], NS[8][2]; /* NS=-1 halt */
static void parse(const char *m){ nst=(strlen(m)+1)/7; for(int s=0;s<nst;s++) for(int y=0;y<2;y++){ const char*t=m+7*s+3*y; if(t[2]=='-'||t[2]-'A'>=nst){NS[s][y]=-1;continue;} W[s][y]=t[0]-'0'; D[s][y]=t[1]=='R'?1:-1; NS[s][y]=t[2]-'A'; } }
/* L stack: top = cell left of head; tokens stored in tape order (left to right) but popped from the right end.
   R stack: top = head cell; tokens stored so that the top's first cell is the head cell. */
stack L,R; int st=0; u128 steps=0;
/* unroll top of R so the top is a literal */
static int rhead(void){ while(1){ if(!R.n) return 0; tok t=R.a[R.n-1]; if(t.len==1&&t.c==1) return t.w; R.n--; if(t.c>1){ tok r=t; r.c--; push_raw(&R,r);} for(int i=t.len-1;i>=0;i--) push_raw(&R,lit(CELL(t,i))); } }
static void lunroll(void){ while(1){ if(!L.n) { push_raw(&L,lit(0)); return; } tok t=L.a[L.n-1]; if(t.len==1&&t.c==1) return; L.n--; if(t.c>1){ tok r=t; r.c--; push_raw(&L,r);} for(int i=0;i<t.len;i++) push_raw(&L,lit(CELL(t,i))); } }
/* mini simulation for crossing */
typedef struct { int ok; uint32_t v; int s; } xres;
#define HS 1<<20
typedef struct { uint64_t key; xres r; int used; } hent;
static hent *H;
static uint64_t hkey(int d,int q,uint32_t u,int ul,uint32_t w,int wl){ return ((uint64_t)d<<60)|((uint64_t)q<<56)|((uint64_t)ul<<52)|((uint64_t)wl<<46)|((uint64_t)u<<23)|w; }
static xres mini(int d,int q,uint32_t u,int ul,uint32_t w,int wl){
  uint64_t k=hkey(d,q,u,ul,w,wl); uint64_t h=(k*0x9E3779B97F4A7C15ULL)>>44; while(H[h].used){ if(H[h].key==k) return H[h].r; h=(h+1)&((HS)-1);}
  xres r={0,0,0}; int c[32]; int n=ul+wl, pos, q0=q;
  if(d==1){ for(int i=0;i<ul;i++) c[i]=(u>>(ul-1-i))&1; for(int i=0;i<wl;i++) c[ul+i]=(w>>(wl-1-i))&1; pos=ul; }
  else { for(int i=0;i<wl;i++) c[i]=(w>>(wl-1-i))&1; for(int i=0;i<ul;i++) c[wl+i]=(u>>(ul-1-i))&1; pos=wl; }
  for(int s=1;s<=400;s++){
    if(pos<0||pos>=n) break; int y=c[pos]; if(NS[q][y]<0) break; c[pos]=W[q][y]; pos+=D[q][y]; q=NS[q][y];
    if(d==1){ if(q==q0 && pos==n){ int okk=1; for(int i=0;i<ul;i++) if(c[wl+i]!=((u>>(ul-1-i))&1)) okk=0; if(okk){ uint32_t v=0; for(int i=0;i<wl;i++) v=(v<<1)|c[i]; r.ok=1;r.v=v;r.s=s;} break; } }
    else { if(q==q0 && pos==-1+0 && 0){} if(q==q0 && pos==0 ){ /* head at position 0 reading u[0]? need left empty: pos==0 */ int okk=1; for(int i=0;i<ul;i++) if(c[i]!=((u>>(ul-1-i))&1)) okk=0; if(okk){ uint32_t v=0; for(int i=0;i<wl;i++) v=(v<<1)|c[ul+i]; r.ok=1;r.v=v;r.s=s;} break; } }
  }
  H[h].used=1;H[h].key=k;H[h].r=r; return r;
}
static int try_cross(void){
  /* right: R top is a run (not literal) */
  if(R.n){ tok t=R.a[R.n-1]; if(!(t.len==1&&t.c==1)){
    for(int lu=0;lu<=3;lu++){ if(L.n<lu) break; int okl=1; uint32_t u=0; for(int i=0;i<lu;i++){ tok x=L.a[L.n-lu+i]; if(!(x.len==1&&x.c==1)){okl=0;break;} u=(u<<1)|x.w; } if(!okl) break;
      xres r=mini(1,st,u,lu,t.w,t.len); if(r.ok){ R.n--; tok us[4]; for(int i=0;i<lu;i++) us[i]=L.a[L.n-lu+i]; L.n-=lu; tok v={r.v,t.len,t.c}; push(&L,v); for(int i=0;i<lu;i++) push_raw(&L,us[i]); steps+=(u128)r.s*t.c; return 1; } } } }
  if(L.n){ tok t=L.a[L.n-1]; if(!(t.len==1&&t.c==1)){
    for(int lu=1;lu<=3;lu++){ if(R.n<lu) break; int okl=1; uint32_t u=0; for(int i=0;i<lu;i++){ tok x=R.a[R.n-1-i]; if(!(x.len==1&&x.c==1)){okl=0;break;} u=(u<<1)|x.w; } if(!okl) break;
      xres r=mini(-1,st,u,lu,t.w,t.len); if(r.ok){ L.n--; tok us[4]; for(int i=0;i<lu;i++) us[i]=R.a[R.n-1-i]; R.n-=lu; tok v={r.v,t.len,t.c};
        /* R stack: push v run (its first cell must come after u) : R stores top=head; v goes below u */
        push(&R,v); for(int i=lu-1;i>=0;i--) push_raw(&R,us[i]); steps+=(u128)r.s*t.c; return 1; } } } }
  return 0;
}
/* tape positions: track head position relative to the start, and extremes */
long long hpos=0, lo=0, hi=0;
static int halted=0; static int nocross=0;
static void step1(void){
  int y=rhead(); if(NS[st][y]<0){ halted=1; steps++; return; }
  if(R.n) R.n--; int w=W[st][y], d=D[st][y]; st=NS[st][y]; steps++;
  if(d==1){ push(&L,lit(w)); hpos++; }
  else { push_raw(&R,lit(w)); lunroll(); tok t=L.a[--L.n]; push_raw(&R,t); hpos--; }
}
/* hpos tracking under crossings */
static long long cross_shift(void){ return 0; }
/* flatten whole tape into a char buffer (only for small tapes / printing) is too costly; instead normalise tokens */
typedef struct { int lit; int b; uint64_t c; } item; /* lit: one bit b; else P-run of count c */
static item *IT; static long nit, capit;
static void addit(item x){ if(nit==capit){capit=capit?2*capit:4096; IT=realloc(IT,capit*sizeof(item));} IT[nit++]=x; }
uint32_t P; int PL;
static void addtok(tok t){
  if(t.len==1&&t.c==1){ item x={1,(int)t.w,0}; addit(x); return; }
  /* is w a rotation of P? */
  for(int r=0;r<PL && t.len==PL;r++){ uint32_t rot=((P<<r)|(P>>(PL-r)))&((1u<<PL)-1); if(rot==t.w){
      /* w = P rotated left by r: w^c = P[r..] (P)^(c-1) P[..r] */
      for(int i=r;i<PL;i++){ item x={1,(int)((P>>(PL-1-i))&1),0}; addit(x);} if(t.c>1){ item x={0,0,t.c-1}; addit(x);} for(int i=0;i<r;i++){ item x={1,(int)((P>>(PL-1-i))&1),0}; addit(x);} return; } }
  for(uint64_t k=0;k<t.c;k++) for(int i=0;i<t.len;i++){ item x={1,(int)CELL(t,i),0}; addit(x);} /* expand others (should be rare) */
}
static void normalise(void){
  nit=0; for(long i=0;i<L.n;i++) addtok(L.a[i]); long hidx=nit; for(long i=R.n-1;i>=0;i--) addtok(R.a[i]);
  /* compress: literal windows equal to P -> run */
  item *o=malloc((nit+8)*sizeof(item)); long m=0, newh=-1;
  for(long i=0;i<nit;){
    if(i==hidx) newh=m;
    int isP=0;
    if(i+PL<=nit && !(hidx>i && hidx<i+PL)){ isP=1; for(int k=0;k<PL;k++){ if(!IT[i+k].lit || IT[i+k].b!=(int)((P>>(PL-1-k))&1)){isP=0;break;} } }
    if(isP){ if(m && !o[m-1].lit && newh!=m){ o[m-1].c+=1; } else { item x={0,0,1}; o[m++]=x; } i+=PL; continue; }
    if(!IT[i].lit){ if(m && !o[m-1].lit && newh!=m){ o[m-1].c+=IT[i].c; } else o[m++]=IT[i]; i++; continue; }
    o[m++]=IT[i]; i++;
  }
  if(newh<0) newh=m;
  L.n=0; R.n=0;
  for(long i=0;i<newh;i++){ if(o[i].lit) push_raw(&L,lit(o[i].b)); else { tok t={P,(uint8_t)PL,o[i].c}; push(&L,t);} }
  for(long i=m-1;i>=newh;i--){ if(o[i].lit) push_raw(&R,lit(o[i].b)); else { tok t={P,(uint8_t)PL,o[i].c}; push_raw(&R,t);} }
  /* R top must be a literal head cell; fine if a run (rhead unrolls) */
  free(o);
}
static void print128(u128 x){ char b[50]; int n=0; if(!x){putchar('0');return;} while(x){b[n++]='0'+(int)(x%10);x/=10;} while(n) putchar(b[--n]); }
static char *OB; static size_t OBn, OBcap;
static void oc(char ch){ if(OBn+2>=OBcap){OBcap=OBcap?2*OBcap:1<<16; OB=realloc(OB,OBcap);} OB[OBn++]=ch; OB[OBn]=0; }
static void os(const char*x){ while(*x) oc(*x++); }
static long ntoks; static uint64_t firstrun;
static void printtape(int rev){ OBn=0; ntoks=0; firstrun=0;
  /* print tokens: runs of P as B<n>, literal stretches as strings; skip head marker; trailing/leading zeros trimmed */
  long tot=L.n+R.n; tok *seq=malloc(tot*sizeof(tok)); long k=0; for(long i=0;i<L.n;i++) seq[k++]=L.a[i]; for(long i=R.n-1;i>=0;i--) seq[k++]=R.a[i];
  /* trim zeros at both ends */
  long a=0,b=tot-1; while(a<=b && seq[a].len==1&&seq[a].w==0) a++; while(b>=a && seq[b].len==1&&seq[b].w==0) b--;
  int inlit=0;
  if(!rev){ for(long i=a;i<=b;i++){ tok t=seq[i]; if(t.len==1&&t.c==1){ if(!inlit){oc(' ');inlit=1;ntoks++;} oc('0'+t.w);} else { inlit=0; if(t.w==P&&t.len==PL) {char b[40]; sprintf(b," B%llu",(unsigned long long)t.c); os(b); ntoks++; if(!firstrun) firstrun=t.c;} else { os(" (");ntoks++; for(int j=0;j<t.len;j++) oc('0'+CELL(t,j)); {char b[40]; sprintf(b,")^%llu",(unsigned long long)t.c); os(b);}} } } }
  else { for(long i=b;i>=a;i--){ tok t=seq[i]; if(t.len==1&&t.c==1){ if(!inlit){oc(' ');inlit=1;ntoks++;} oc('0'+t.w);} else { inlit=0; if(t.w==P&&t.len==PL) {char b[40]; sprintf(b," B%llu",(unsigned long long)t.c); os(b); ntoks++; if(!firstrun) firstrun=t.c;} else { os(" (");ntoks++; for(int j=t.len-1;j>=0;j--) oc('0'+CELL(t,j)); {char b[40]; sprintf(b,")^%llu",(unsigned long long)t.c); os(b);}} } } }
  free(seq);
}
int main(int argc,char**argv){
  parse(argv[1]); double maxs=atof(argv[2]); int side=argv[3][0]=='R'?1:-1; int SS=argv[4][0]-'A';
  PL=strlen(argv[5]); P=0; for(int i=0;i<PL;i++) P=(P<<1)|(argv[5][i]-'0');
  long long every=atoll(argv[6]); long long maxsw=argc>7?atoll(argv[7]):-1;
  int Fst = argc>8 ? argv[8][0]-'A' : 5; int quietF = argc>9 ? atoi(argv[9]) : 0; nocross = getenv("RL_NOCROSS") != 0; long long nF=0;
  H=calloc(HS,sizeof(hent));
  u128 MAX=(u128)maxs; long long sw=0; long pntoks=-1; uint64_t pfirst=0; int fev=0, pprinted=1; char *pbuf=0; u128 psteps=0;
  /* head position tracking: we need "fresh cell on the growing side": detect R empty (side R) after moving right. */
  while(steps<MAX && !halted){
    int prev=st;
    if(nocross || !try_cross()){ step1(); if(halted) break; }
    if(st==Fst && prev!=Fst){ int sym=rhead(); nF++; if(!quietF || sym){ printf("F "); print128(steps); printf(" %d\n", sym); fev=1; } }
    int fresh = side==1 ? (R.n==0) : (L.n==0);
    if(fresh && st==SS){ normalise(); printtape(side==-1);
      sw++;
      if(every>0){ if(sw%every==0){ printf("S "); print128(steps); printf("%s\n",OB);} }
      else { int interesting = (ntoks!=pntoks) || (firstrun!=pfirst) || fev;
        if(interesting){ if(!pprinted && pbuf){ printf("S "); print128(psteps); printf("%s\n",pbuf);} printf("S "); print128(steps); printf("%s\n",OB); }
        pprinted=interesting; fev=0; pntoks=ntoks; pfirst=firstrun; psteps=steps; pbuf=realloc(pbuf,OBn+1); memcpy(pbuf,OB,OBn+1); }
      if(maxsw>0&&sw>=maxsw) break; }
  }
  if(halted){ printf("halted "); print128(steps); putchar('\n'); }
  else { printf("running "); print128(steps); printf(" sweeps %lld Fentries %lld\n",sw,nF); }
  return 0;
}
