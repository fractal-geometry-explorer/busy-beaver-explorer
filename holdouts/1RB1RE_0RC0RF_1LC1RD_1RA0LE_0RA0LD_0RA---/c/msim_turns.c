/* msim_turns: msim.c of holdouts/1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/c with two more output modes:
 *   t  a line at every reversal of the head (between macro steps);
 *   b  a line after every run crossed at once with at least EVERY copies.
 * The simulation itself is unchanged.  Original header:
 *
 * msim MACHINE K MAXSTEPS [CFG|-] [EVERY] [r|l]
 *
 * A macro simulator for machines whose tape is long runs of one repeated word that the head sweeps across.
 * The tape is two stacks of runs (block of K cells, count).  One macro step simulates the machine on a window of two
 * blocks: the block the head faces and the block behind it (sweeps that look one cell back into the block they have
 * just rewritten, like the zig-zag of 1RB0LB_1RC0LA_..., fit in it), until the head leaves the window.  When the head
 * comes out of the far side of the faced block in the state it entered with, and the same window rule applied with
 * the block it just wrote behind it gives the same block again (a steady state), all the remaining copies of the
 * faced run are crossed at once: k copies, k times the steps of one.  Otherwise the window is updated and the head
 * moves on (or turns back).  Exact: every macro step is a run of the machine, counted step for step (bbchallenge
 * count, 128-bit), and a steady state crossing is the same run k times.  Checked against the direct simulator
 * (tools/c/tm.h) by py/check_msim.py.
 *
 * Output: a line each time the head enters a fresh blank block on the right (r, default) or left (l), every EVERY-th
 * time: "STEPS S> blocks | blocks" (S< when the head faces left), blocks as bits^count; "HALT ..." on a halt.
 * CFG: a start configuration "STATE HEADINDEX BITS" (head on BITS[HEADINDEX], facing right); "-" for blank tape.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned __int128 u128;
typedef struct { uint32_t v; uint64_t n; } run;
static int K, NS; static int W[8][2], D[8][2], S[8][2];
static run *L, *R; static long nl, nr, cap=1<<22;
#define INF (1ULL<<62)
typedef struct { uint8_t res; /*0 far,1 back,2 halt,3 loop*/ uint8_t ns; uint32_t nt, nb; uint32_t steps; } tr;
static tr *T; /* index: ((s*2+dir)<<(2K)) | (top<<K) | behind */
static inline long tix(int s,int dir,uint32_t top,uint32_t beh){ return ((long)(s*2+dir)<<(2*K)) | ((long)top<<K) | beh; }
static void build(){
  long n=(long)NS*2<<(2*K); T=calloc(n,sizeof(tr));
  for(int s=0;s<NS;s++) for(int dir=0;dir<2;dir++) for(uint32_t top=0;top<(1u<<K);top++) for(uint32_t beh=0;beh<(1u<<K);beh++){
    int c[32]; /* window cells left to right */
    uint32_t lb = dir? beh: top, rb = dir? top: beh;
    for(int i=0;i<K;i++){ c[i]=(lb>>(K-1-i))&1; c[K+i]=(rb>>(K-1-i))&1; }
    int p = dir? K : K-1; int st=s; uint32_t k=0; tr t={0};
    while(p>=0 && p<2*K){
      if(k>1000000){ t.res=3; break; }
      int y=c[p]; if(S[st][y]<0){ t.res=2; break; }
      c[p]=W[st][y]; p+=D[st][y]; st=S[st][y]; k++;
    }
    if(t.res<2){
      int far = dir? (p>=2*K) : (p<0);
      t.res = far?0:1;
    }
    uint32_t nl_=0,nr_=0; for(int i=0;i<K;i++){ nl_=nl_*2+c[i]; nr_=nr_*2+c[K+i]; }
    t.nt = dir? nr_: nl_; t.nb = dir? nl_: nr_; t.ns=st; t.steps=k;
    T[tix(s,dir,top,beh)]=t;
  }
}
static inline void push(run*S_,long*n,uint32_t v,uint64_t c){ if(*n&&S_[*n-1].v==v&&S_[*n-1].n<INF){S_[*n-1].n+=c;return;} if(*n==cap){fprintf(stderr,"cap\n");exit(1);} S_[*n].v=v;S_[*n].n=c;(*n)++; }
static inline void pop1(run*S_,long*n){ if(S_[*n-1].n>=INF) return; if(S_[*n-1].n==1)(*n)--; else S_[*n-1].n--; }
static void prbits(uint32_t v){ for(int i=K-1;i>=0;i--) putchar('0'+((v>>i)&1)); }
static void prs(u128 x){ char b[50]; int i=49; b[i]=0; if(!x){putchar('0');return;} while(x){b[--i]='0'+(int)(x%10); x/=10;} fputs(b+i,stdout); }
static void dump(u128 steps,int st,int dir){
  prs(steps); printf(" %c%c", 'A'+st, dir?'>':'<');
  for(long i=0;i<nl;i++){ if(L[i].n>=INF) continue; putchar(' '); prbits(L[i].v); if(L[i].n>1) printf("^%llu",(unsigned long long)L[i].n);}
  printf(" |");
  for(long j=nr-1;j>=0;j--){ if(R[j].n>=INF) continue; putchar(' '); prbits(R[j].v); if(R[j].n>1) printf("^%llu",(unsigned long long)R[j].n);}
  putchar('\n'); fflush(stdout);
}
int main(int argc,char**argv){
  const char*m=argv[1]; K=atoi(argv[2]); long double maxd=strtold(argv[3],0); u128 maxs=(u128)maxd;
  NS=(strlen(m)+1)/7;
  for(int s=0;s<NS;s++) for(int y=0;y<2;y++){ const char*t=m+7*s+3*y; if(t[2]=='-'){S[s][y]=-1;W[s][y]=0;D[s][y]=0;} else {W[s][y]=t[0]-'0'; D[s][y]=t[1]=='R'?1:-1; S[s][y]=t[2]-'A';}}
  build(); L=malloc(sizeof(run)*cap); R=malloc(sizeof(run)*cap);
  push(L,&nl,0,INF); push(R,&nr,0,INF);
  int st=0, dir=1; long every = argc>5? atol(argv[5]):1; int mode= argc>6? argv[6][0]:'r';
  if(argc>4 && strcmp(argv[4],"-")){ FILE*f=fopen(argv[4],"r"); char sc; long hidx; static char b[1<<25], bb[1<<25];
    if(fscanf(f," %c %ld %s",&sc,&hidx,b)!=3) return 1; fclose(f); st=sc-'A'; long n=strlen(b);
    long pad=(K-hidx%K)%K; memset(bb,'0',pad); strcpy(bb+pad,b); hidx+=pad; n+=pad;
    while(n%K) bb[n++]='0'; bb[n]=0;
    for(long i=0;i<hidx;i+=K){ uint32_t v=0; for(int j=0;j<K;j++) v=v*2+(bb[i+j]-'0'); push(L,&nl,v,1);}
    for(long i=n-K;i>=hidx;i-=K){ uint32_t v=0; for(int j=0;j<K;j++) v=v*2+(bb[i+j]-'0'); push(R,&nr,v,1);}
  }
  u128 steps=0; long ev=0; uint64_t ms=0;
  while(steps<maxs){
    ms++;
    run *F = dir? R:L, *B = dir? L:R; long *nf = dir? &nr:&nl, *nb = dir? &nl:&nr;
    uint32_t top=F[*nf-1].v, beh=B[*nb-1].v; uint64_t cnt=F[*nf-1].n;
    int fresh = (F[*nf-1].n>=INF);
    tr t=T[tix(st,dir,top,beh)];
    if(t.res==3){ printf("LOOP "); dump(steps,st,dir); return 0; }
    if(t.res==2){ steps+=t.steps+1; printf("HALT "); dump(steps,t.ns,dir); return 0; }
    steps+=t.steps;
    if(t.res==0){
      pop1(F,nf); pop1(B,nb); push(B,nb,t.nb,1); push(B,nb,t.nt,1);
      if(t.ns==st && !fresh && cnt>=2){
        tr u=T[tix(st,dir,top,t.nt)];
        if(u.res==0 && u.ns==st && u.nt==t.nt){
          uint64_t k=cnt-1;
          /* remove k copies of top from the facing run */
          if(F[*nf-1].v==top && F[*nf-1].n>=k && F[*nf-1].n<INF){ F[*nf-1].n-=k; if(F[*nf-1].n==0) (*nf)--; }
          else { fprintf(stderr,"bad run\n"); exit(1); }
          pop1(B,nb); push(B,nb,u.nb,k); push(B,nb,u.nt,1); steps+=(u128)k*u.steps; if(mode=='b'&&k>=(uint64_t)every){ st=t.ns; dump(steps,st,dir);}
        }
      }
      st=t.ns;
    } else {
      /* head went back past the behind block: both blocks now on the facing side of the new direction */
      pop1(F,nf); pop1(B,nb); push(F,nf,t.nt,1); push(F,nf,t.nb,1); st=t.ns; dir=!dir; if(mode=='t') dump(steps,st,dir);
    }
    if(fresh && ((mode=='r'&&F==R)||(mode=='l'&&F==L))){ ev++; if(ev%every==0) dump(steps,st,dir); }
  }
  printf("END ms=%llu ",(unsigned long long)ms); dump(steps,st,dir); return 0;
}
