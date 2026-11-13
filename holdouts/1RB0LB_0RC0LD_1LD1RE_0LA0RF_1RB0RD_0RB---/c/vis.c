// Visit-accelerated simulator. See vis.py for the prototype (same algorithm, Python ints).
// visit: head in state SIN at q with cell q-1 == 0  ->  head in state SOUT at q-2, cell q-1 == 0, only cells >= q changed.
// Counts are 2^e - c (big) or exact 128-bit.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
typedef unsigned __int128 u128;
typedef struct { int big; int64_t e; u128 c; } cnt;   // big: 2^e - c ; else c
#define DIE(...) do { fprintf(stderr, __VA_ARGS__); fprintf(stderr, "\n"); report(); exit(3); } while (0)
static int tmw[6][2], tmd[6][2], tms[6][2];
#define TSZ (1L<<31)
static uint8_t *tape0, *tape; static long lo=0, hi=0;
static int SIN=2, SOUT=0;
static long topvis=0, nsingle=0, nraw=0, rawsteps=0, nbatchsteps=0, maxround=0;
static int nrules=0; static int depth=0, maxdepth=0;
#define MAXW 12
typedef struct { uint8_t valid, k; uint16_t out; } rule;
static rule *rules[MAXW+1];
typedef struct { int stamp; uint8_t ok, W, L; uint8_t k[4]; uint16_t fin[4]; } cyc;
static cyc cycs[1<<MAXW];
static void report(void); static void dump(long pos);
static cnt one(void){ cnt r={0,0,1}; return r; }
static cnt norm(cnt n){
  if(n.big){
    if(n.e<=100){ u128 v=((u128)1<<n.e); if(n.c>v) { fprintf(stderr,"norm neg\n"); exit(4);} n.big=0; n.c=v-n.c; n.e=0; }
    else if(n.c>>100){ fprintf(stderr,"big c overflow\n"); exit(4); }
  } else if(n.c>>110){ int e=0; while(e<127 && ((u128)1<<e)<n.c) e++; u128 c=((u128)1<<e)-n.c;
    if(c>>90){ fprintf(stderr,"exact overflow\n"); exit(4); } n.big=1; n.e=e; n.c=c; }
  return n; }
static inline int win(long p,int w){ int b=0; for(int i=0;i<w;i++) b|=tape[p+i]<<i; return b; }
static inline void setwin(long p,int w,int b){ for(int i=0;i<w;i++) tape[p+i]=(b>>i)&1; if(p+w>hi) hi=p+w; }
static void batch(long p, cnt n);
static void halt(int st,int c,long pos);
static void raw(long p, int top){
  long pos=p, tmax= top? p-1 : p, q=-1, tmin=p; int st= top?0:SIN, nsub=0, reg=1; long n=0;
  int init=0, seen=0; // initial bits of cells p..p+MAXW-1 as first read
  nraw++;
  for(;;){
    if(st==SIN && tape[pos-1]==0 && (top || pos>tmax)){
      if(top){ topvis++; if(maxround && topvis>maxround){ report(); dump(pos); exit(0);} if((topvis&1023)==0) report(); }
      if(nsub==0) q=pos; else if(q!=pos) reg=0;
      nsub++; batch(pos, one()); pos-=2; st=SOUT;
      if(!top && pos<=p-2) DIE("sub returned outside");
      continue;
    }
    int c=tape[pos];
    if(pos>tmax) tmax=pos;
    if(!top){ long o=pos-p; if(o>=0 && o<MAXW && !((seen>>o)&1)){ seen|=1<<o; init|=c<<o; } }
    if(tmw[st][c]<0){ halt(st,c,pos); }
    tape[pos]=tmw[st][c]; if(pos>=hi) hi=pos+1; if(pos<lo) lo=pos;
    pos+=tmd[st][c]; st=tms[st][c]; n++; rawsteps++;
    if(!top && n>100000000) DIE("raw visit too long at %ld",p);
    if(!top && pos==p-2){ if(st!=SOUT||tape[p-1]!=0) DIE("bad return st=%d at %ld",st,p); break; }
  }
  long w;
  if(nsub){ if(!reg||tmax>=q) return; w=q-p; } else w=tmax+1-p;
  if(w>MAXW || w<1) return;
  if((seen&((1<<w)-1))!=(1<<w)-1) return;
  rule *r=&rules[w][init&((1<<w)-1)];
  if(!r->valid){ r->valid=1; r->k=nsub; r->out=win(p,w); nrules++;
    fprintf(stderr,"rule w=%ld ",w); for(int i=0;i<w;i++) fputc('0'+((init>>i)&1),stderr); fprintf(stderr," -> ");
    for(int i=0;i<w;i++) fputc('0'+tape[p+i],stderr); fprintf(stderr," subs=%d (topvis %ld)\n",nsub,topvis); }
}
static int match(int buf,int *w){ for(int i=1;i<=MAXW;i++){ rule *r=&rules[i][buf&((1<<i)-1)]; if(r->valid){ *w=i; return 1; } } return 0; }
static cyc *findcycle(long p){
  int b0=win(p,MAXW); cyc *cy=&cycs[b0];
  if(cy->stamp==nrules+1) return cy->ok?cy:NULL;
  cy->stamp=nrules+1; cy->ok=0;
  int buf=b0, ws[4], ks[4], bs[4];
  for(int L=1;L<=4;L++){
    int w; if(!match(buf,&w)) break;
    rule *r=&rules[w][buf&((1<<w)-1)];
    buf=(buf&~((1<<w)-1))|r->out; ws[L-1]=w; ks[L-1]=r->k; bs[L-1]=buf;
    int sw=0, W=0, bad=0;
    for(int i=0;i<L;i++){ if(ks[i]>0){ if(sw&&sw!=ws[i]) bad=1; sw=ws[i]; } if(ws[i]>W) W=ws[i]; }
    if(bad) break;
    if(sw && W>sw) continue;
    if(L==3) continue;
    if((buf&((1<<W)-1))==(b0&((1<<W)-1))){ cy->ok=1; cy->W=W; cy->L=L; for(int i=0;i<L;i++){ cy->k[i]=ks[i]; cy->fin[i]=bs[i]&((1<<W)-1);} break; }
  }
  return cy->ok?cy:NULL;
}
static int ilog2x(int M){ int m=0; while((1<<m)<M) m++; if((1<<m)!=M) return -1; return m; }
static void batch(long p, cnt n){
  if(++depth>maxdepth) maxdepth=depth;
  for(;;){
    if(!n.big && n.c==0) break;
    if(p+2*MAXW>=TSZ/2) DIE("tape overflow");
    nbatchsteps++;
    cyc *cy=findcycle(p);
    if(cy){
      int L=cy->L, M=0, l=(L==1?0:L==2?1:2); for(int i=0;i<L;i++) M+=cy->k[i];
      int rem; cnt tot;
      if(n.big){
        rem=(int)((L-(int)(n.c%L))%L); u128 cc=(n.c+L-1)/L;   // full = 2^(e-l) - cc
        int part=0; for(int i=0;i<rem;i++) part+=cy->k[i];
        if(M==0){ tot.big=0; tot.e=0; tot.c=part; }
        else { int m=ilog2x(M); if(m<0) DIE("M=%d not a power of two in big mode",M);
          u128 c2=cc<<m; if(c2<(u128)part) DIE("negative c"); tot.big=1; tot.e=n.e-l+m; tot.c=c2-part; }
      } else {
        u128 full=n.c/L; rem=(int)(n.c%L); int part=0; for(int i=0;i<rem;i++) part+=cy->k[i];
        tot.big=0; tot.e=0; tot.c=full*M+part;
      }
      setwin(p,cy->W, rem? cy->fin[rem-1] : cy->fin[L-1]);
      p+=cy->W; n=norm(tot); continue;
    }
    nsingle++;
    int w, b=win(p,MAXW);
    if(match(b,&w)){ rule *r=&rules[w][b&((1<<w)-1)]; setwin(p,w,r->out); if(r->k){ cnt k={0,0,r->k}; batch(p+w,k);} }
    else raw(p,0);
    if(n.big) n.c+=1; else n.c-=1;
    n=norm(n);
  }
  depth--;
}
static time_t t0;
static void report(void){
  long ones=0; for(long i=lo;i<hi;i++) ones+=tape[i];
  fprintf(stderr,"topvis %ld lo %ld hi %ld ones %ld singles %ld raws %ld rawsteps %ld bsteps %ld rules %d maxdepth %d t %lds\n",
    topvis,lo,hi,ones,nsingle,nraw,rawsteps,nbatchsteps,nrules,maxdepth,(long)(time(0)-t0));
}
static const char *dumpfile=NULL;
static void dump(long pos){ if(dumpfile){ long a=lo,b=hi; while(a<b&&!tape[a])a++; while(b>a&&!tape[b-1])b--; FILE *f=fopen(dumpfile,"w"); fprintf(f,"%ld %ld %ld\n",a,b,pos); for(long i=a;i<b;i++) fputc('0'+tape[i],f); fputc('\n',f); fclose(f);} }
static void halt(int st,int c,long pos){
  printf("HALT state %c reading %d at pos %ld during top visit %ld depth %d\n",'A'+st,c,pos,topvis,depth);
  printf("window: "); for(long i=pos-40;i<=pos+40;i++){ if(i==pos) putchar('['); putchar('0'+tape[i]); if(i==pos) putchar(']'); } putchar('\n');
  report();
  dump(pos);
  exit(0);
}
int main(int argc,char **argv){
  const char *s=argv[1]; if(argc>2) maxround=atol(argv[2]); if(argc>3) dumpfile=argv[3];
  for(int q=0;q<6;q++) for(int c=0;c<2;c++){ const char *t=s+q*7+c*3;
    if(t[0]=='-'){ tmw[q][c]=-1; } else { tmw[q][c]=t[0]-'0'; tmd[q][c]=t[1]=='R'?1:-1; tms[q][c]=t[2]-'A'; } }
  tape0=calloc(TSZ,1); tape=tape0+TSZ/2;
  for(int i=1;i<=MAXW;i++) rules[i]=calloc(1<<i,sizeof(rule));
  t0=time(0);
  raw(0,1);
  return 0;
}
