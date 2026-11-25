/* Round trips of 1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB as a cellular automaton (lean/Trip.lean, `trip`).

   A trip starts when the head first stands on a new leftmost cell (state A, blank). Let Q be the first cell with
   c[Q] = c[Q+1] = 0. If the stretch up to Q has no isolated 1 (0 1 0), Trip.lean proves the trip: cells lo..Q become
   c'[p] = 1 ^ c[p] ^ c[p+3] (with a virtual 1 1 0 after Q), c[Q+1] becomes 1, the head ends at lo-1 in A, after
   4(Q-lo) - 6z + 15 steps (z = zeros in lo..Q+1). Such trips are done here with 64-bit word operations; every other
   trip (an isolated 1 before Q, i.e. the right sweep's token mode, the trips that reach the right end, and the
   three-step trips where Q = lo) is run on the machine's own table, cell by cell.

   usage: ./trips NTRIPS MODE [REPORT]
     MODE 0: fast.  MODE 1: also run every CA trip on the machine and compare the whole tape (validation).
   Prints ISO for every trip with an isolated 1 before Q (token mode, where a halt would happen), PRE for every trip
   whose turn point ends an all-y segment (zeros every 3 cells) with a 3-cell wall (111) on its left, which is how
   every bulk 10 defect of the run was born, and a status line every REPORT trips.  A halt would print HALT.
   With the environment variable TL=n it also prints the last n cells (TL trip hi cells) whenever they change
   (input for py/rend_cycle.py). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint64_t u64;
static int W[6][2],D[6][2],S[6][2];
static long NB; static u64 *t,*t2;
#define GET(a,p) ((int)(((a)[(p)>>6]>>((p)&63))&1))
#define SET(a,p,v) do{ if(v) (a)[(p)>>6]|=1ULL<<((p)&63); else (a)[(p)>>6]&=~(1ULL<<((p)&63)); }while(0)
static long lo,hi,steps;
/* the machine from the head at lo in A until it first stands on lo-1; 0 if it halts */
static int runtrip(u64*a,long *nsteps,long *mxout){
  long p=lo; int s=0; long n=0; long mx=p;
  for(;;){ int r=GET(a,p); if(S[s][r]<0){*nsteps=n;return 0;} SET(a,p,W[s][r]); int d=D[s][r]; s=S[s][r]; p+=d; n++;
    if(p>mx)mx=p;
    if(p<lo){ if(s!=0){fprintf(stderr,"state %d at new left cell\n",s);exit(1);} *nsteps=n; *mxout=mx; return 1;} }
}
static long firstQ(u64*a,long from,long to){
  for(long w=from>>6; (w<<6)<to; w++){
    u64 m=~a[w] & ~((a[w]>>1)|(a[w+1]<<63));
    if(w==(from>>6)) m&= ~0ULL<<(from&63);
    if(m){ long p=(w<<6)+__builtin_ctzll(m); return p<to?p:-1; }
  }
  return -1;
}
static long firstIso(u64*a,long from,long to){
  for(long w=from>>6; (w<<6)<=to; w++){
    u64 c=a[w], l=(a[w]<<1)|(w?a[w-1]>>63:0), r=(a[w]>>1)|(a[w+1]<<63);
    u64 m=c&~l&~r; if(w==(from>>6)) m&= ~0ULL<<(from&63);
    if(m){ long p=(w<<6)+__builtin_ctzll(m); return p<=to?p:-1; }
  }
  return -1;
}
static void ca(u64*a,long Q){
  long A=lo-2, B=Q-3;
  int vq1=1^GET(a,Q-1)^GET(a,Q+2);
  long wa=A>>6, wb=B>>6;
  for(long w=wa; w<=wb; w++){
    u64 nv=~(a[w]^((a[w]>>3)|(a[w+1]<<61)));
    u64 m=~0ULL; if(w==wa) m&=~0ULL<<(A&63); if(w==wb) m&= (B&63)==63?~0ULL:((1ULL<<((B&63)+1))-1);
    a[w]=(a[w]&~m)|(nv&m);
  }
  SET(a,Q-2,1); SET(a,Q-1,vq1); SET(a,Q,1); SET(a,Q+1,1);
}
static long zeros(u64*a,long a0,long a1){ long z=0,p=a0; for(;p<=a1&&(p&63);p++) z+=!GET(a,p);
  for(;p+63<=a1;p+=64) z+=64-__builtin_popcountll(a[p>>6]);
  for(;p<=a1;p++) z+=!GET(a,p);
  return z; }
int main(int argc,char**argv){
  const char*T="1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB";
  for(int i=0;i<6;i++)for(int r=0;r<2;r++){const char*g=T+7*i+3*r; if(g[0]=='-'){S[i][r]=-1;continue;} W[i][r]=g[0]-'0';D[i][r]=g[1]=='R'?1:-1;S[i][r]=g[2]-'A';}
  if(argc<3){fprintf(stderr,"usage: %s NTRIPS MODE [REPORT]\n",argv[0]);return 1;}
  long ntrips=atol(argv[1]); int mode=atoi(argv[2]); long rep=argc>3?atol(argv[3]):1000000;
  NB=(ntrips/32)+(1L<<16); /* words: two cells of room per trip on each side */
  t=calloc(NB,8); t2=mode?calloc(NB,8):0; if(!t||(mode&&!t2)){fprintf(stderr,"no memory\n");return 1;}
  long st=(NB<<6)/2; lo=hi=st;
  { long p=st; int s=0; for(;;){ int r=GET(t,p); SET(t,p,W[s][r]); int d=D[s][r]; s=S[s][r]; p+=d; steps++; if(p>hi)hi=p; if(p<lo){lo=p;break;} } }
  long tl=getenv("TL")?atol(getenv("TL")):0; static char tlcur[4096],tlprev[4096]; if(tl>4000) tl=4000;
  long nca=0,ntm=0,niso=0,npre=0,bad=0;
  for(long k=0;k<ntrips;k++){
    long Q=firstQ(t,lo,(NB<<6)-128);
    int useca=(Q-lo>=8) && Q>=0 && Q+3<hi; long iso=-1;
    if(useca){ iso=firstIso(t,lo+2,Q+1); if(iso>=0){ useca=0; niso++;
        printf("ISO trip %ld step %ld: isolated 1 at lo+%ld, %ld cells before the turn, %ld from the right end\n",k,steps,iso-lo,Q-iso,hi-iso);} }
    if(useca){
      /* the segment ending at Q: zeros at Q, Q-3, ... back to the first zero of another residue */
      long p,last=Q; int ally=1;
      for(p=Q-1;p>lo;p--) if(!GET(t,p)){ if((Q-p)%3==0){ if(last-p!=3) ally=0; last=p; } else break; }
      if(ally && last-p==4 && p>lo+20){ npre++; printf("PRE trip %ld step %ld: all-y segment of %ld words ends at the turn, 111 wall on its left, %ld cells from the right end\n",k,steps,(Q-last)/3+1,hi-Q); }
      long z=zeros(t,lo,Q+1);
      if(mode){ long w0=(lo-64)>>6, w1=(Q+256)>>6; memcpy(t2+w0,t+w0,8*(w1-w0)); }
      ca(t,Q); nca++;
      if(mode){ long ns,mx; if(!runtrip(t2,&ns,&mx)){printf("HALT in validation\n");return 0;}
        if(ns!=4*(Q-lo)-6*z+15){ bad++; printf("STEPCOUNT trip %ld\n",k);} 
        long w0=(lo-64)>>6, w1=(Q+256)>>6; if(memcmp(t2+w0,t+w0,8*(w1-w0))){ bad++; printf("MISMATCH trip %ld\n",k);} }
      steps+=4*(Q-lo)-6*z+15;
    } else {
      long ns,mx; if(!runtrip(t,&ns,&mx)){ printf("HALT at trip %ld step %ld\n",k,steps+ns); return 0; }
      steps+=ns; ntm++; if(mx>hi)hi=mx;
      if(mode){ long w0=(lo-64)>>6, w1=(mx+256)>>6; memcpy(t2+w0,t+w0,8*(w1-w0)); }
    }
    if(tl>0){ long Qn=useca?Q:hi; if(Qn>=hi-tl-1){ char *cur=tlcur; for(long p=hi-tl+1;p<=hi;p++) cur[p-(hi-tl+1)]='0'+GET(t,p); cur[tl]=0;
        if(strcmp(cur,tlprev)){ printf("TL %ld %ld %s\n",k,hi,cur); strcpy(tlprev,cur);} } }
    lo=lo-1;
    if(lo<128||hi>(NB<<6)-256){fprintf(stderr,"tape full\n");return 1;}
    if((k+1)%rep==0){ printf("trips %ld steps %ld width %ld: %ld by the CA, %ld on the machine, %ld ISO, %ld PRE, %ld mismatches\n",k+1,steps,hi-lo,nca,ntm,niso,npre,bad); fflush(stdout);}
  }
  printf("END trips %ld steps %ld: no halt; %ld ISO, %ld PRE, %ld mismatches (mode %d)\n",ntrips,steps,niso,npre,bad,mode);
}
