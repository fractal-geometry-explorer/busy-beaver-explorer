/* resetsim: the sweep map of a machine whose tape is  (growing end) WORD^n REST (fixed end), with the block shrunk.
 *
 *   resetsim MACHINE SIDE STATE WORD N0 Q SWEEPS [check]
 *
 * A *trigger* is a step at which the head extends the visited cells on SIDE (L or R) in STATE.  At each trigger the
 * cells read from the head towards the fixed end are  c0 PREFIX WORD^n REST ;  the program replaces n by
 * N0 + (n - N0) mod Q (when n >= N0) and runs on.  If crossing the block does not depend on its length, the REST
 * seen at each trigger is the true one: `check` runs the true machine for SWEEPS triggers next to the reset one and
 * compares REST (and n mod Q) at every trigger; a mismatch (an *event*: the run does depend on n there) is printed
 * and the reset run is re-synchronised from the true one.
 *
 * Without `check`: SWEEPS triggers of the reset run, with Brent's cycle detection on the whole (shrunk)
 * configuration, a message when the configuration length changes, and HALTS if the machine halts (a halt of the
 * reset run is a halt of the true run as long as no event happened before it).
 *
 * Environment: T0=k starts the reset run from the true configuration at trigger k; PREFIX=cells (see above);
 * FRONT=1 prints, at powers of two of sweeps, how close to the fixed end a cell has changed (EXCL=e ignores the last
 * e cells); PFROM, PTO, PEV print the configurations of those sweeps; STOPEV=1 stops at the first length change.
 * Build: gcc -O2 -o resetsim resetsim.c -I tools/c   (from the repository root).
 */
#include "tm.h"
typedef struct { unsigned char *c; int len; int st; } conf;  // cells from growing end (head cell first) to fixed end
static tm_machine M; static int SIDE, S0, WL, N0, Q; static unsigned char W[64];
#define CAP (1<<22)
static unsigned char tape[CAP]; static long long head, lo, hi; static int st;
static int loaded=0; static void load(const unsigned char *c,int len,int s){ if(!loaded){memset(tape,0,CAP);loaded=1;} else memset(tape+lo-2,0,hi-lo+5); long long base=CAP/2;
  for(int i=0;i<len;i++){ long long p= SIDE==0? base+i: base-i; tape[p]=c[i]; }
  head=base; lo= SIDE==0? base: base-len+1; hi= SIDE==0? base+len-1: base; st=s; }
static int rest_off(const unsigned char *c,int len,int *nout){ // c[0]=head cell; block starts at c[1+PL]
  static int PL=-1; static unsigned char PF[64]; if(PL<0){ const char*p=getenv("PREFIX"); PL=p?strlen(p):0; for(int j=0;j<PL;j++)PF[j]=p[j]-'0'; }
  if(PL && (len<1+PL || memcmp(c+1,PF,PL))){*nout=0; return 1;}
  int i=1+PL,n=0; while(i+WL<=len && !memcmp(c+i,W,WL)){i+=WL;n++;} *nout=n; return i; }
// run until trigger; returns 0 halted, 1 trigger; steps counted
static long long steps;
static int run_to_trigger(long long maxs){
  long long lo0, hi0;
  for(long long k=0;k<maxs;k++){
    lo0=lo; hi0=hi; int y=tape[head]; int s=M.s[st][y]; if(s<0) return 0;
    tape[head]=M.w[st][y]; head+=M.d[st][y]; st=s; steps++;
    if(head<lo)lo=head; if(head>hi)hi=head;
    if(head<=1||head>=CAP-2){fprintf(stderr,"tape overflow\n");exit(3);}
    if(st==S0 && ((SIDE==0 && head==lo && lo<lo0) || (SIDE==1 && head==hi && hi>hi0))) return 1;
  }
  return 2;
}
static int extract(unsigned char *c){ int len=(int)(hi-lo+1); for(int i=0;i<len;i++) c[i]= SIDE==0? tape[lo+i]: tape[hi-i]; return len; }
static int shrink(unsigned char *c,int len,unsigned char *out){ int n; int r=rest_off(c,len,&n); if(n<N0) { memcpy(out,c,len); return len; }
  int n2=N0+((n-N0)%Q); int L=0; int PLx=r-n*WL; memcpy(out,c,PLx); L=PLx; for(int j=0;j<n2;j++){memcpy(out+L,W,WL);L+=WL;} memcpy(out+L,c+r,len-r); return L+len-r; }
static unsigned long long hsh(const unsigned char*c,int len,int s){ unsigned long long h=1469598103934665603ULL^s; for(int i=0;i<len;i++) h=(h^c[i])*1099511628211ULL; return h^(unsigned long long)len*31; }
static unsigned char A[1<<20],B[1<<20],P[1<<20];
int main(int argc,char**argv){
  tm_parse(argv[1],&M); SIDE=argv[2][0]=='R'; S0=argv[3][0]-'A'; WL=strlen(argv[4]); for(int i=0;i<WL;i++)W[i]=argv[4][i]-'0';
  N0=atoi(argv[5]); Q=atoi(argv[6]); long long MAXS=atoll(argv[7]); int check=argc>8;
  unsigned char z=0; load(&z,1,0);
  long long T0= getenv("T0")? atoll(getenv("T0")):0;
  if(T0){ long long c=0; while(c<T0){ if(run_to_trigger(1LL<<40)!=1){printf("halt in true prefix\n");return 0;} c++; }
    int len=extract(A); int n; int r=rest_off(A,len,&n); printf("start at trigger %lld steps %lld n=%d rest=%d\n",T0,steps,n,len-r); len=shrink(A,len,B); load(B,len,st); }
  if(check){ // true run, record rest hashes, compare with reset run
    long long nsw=MAXS; unsigned long long *hs=malloc(8*nsw); long long cnt=0;
    tm_tape t; tm_tape_init(&t,1<<16); int s=0; long long k=0;
    while(cnt<nsw){ long long l0=t.lo,h0=t.hi; k++; if(!tm_step(&M,&t,&s)){printf("true run halts at %lld\n",k);break;}
      if(s==S0 && ((SIDE==0&&t.head==t.lo&&t.lo<l0)||(SIDE==1&&t.head==t.hi&&t.hi>h0))){ int len=t.hi-t.lo+1; for(int i=0;i<len;i++) A[i]= SIDE==0? tm_get(&t,t.lo+i): tm_get(&t,t.hi-i);
        int n; int r=rest_off(A,len,&n); hs[cnt++]=hsh(A+r,len-r,s)^((unsigned long long)(n%Q)<<50); } }
    printf("true run: %lld triggers in %lld steps\n",cnt,k);
    // second true run to resync at mismatches
    tm_tape t2; tm_tape_init(&t2,1<<16); int s2=0; long long mism=0, c2=0;
    for(long long i=0;i<cnt;i++){ int rr=run_to_trigger(1LL<<40); if(rr!=1){printf("reset run stopped %d at %lld\n",rr,i);return 1;}
      // advance true run t2 to trigger i
      int len2;
      while(1){ long long l0=t2.lo,h0=t2.hi; tm_step(&M,&t2,&s2); if(s2==S0 && ((SIDE==0&&t2.head==t2.lo&&t2.lo<l0)||(SIDE==1&&t2.head==t2.hi&&t2.hi>h0))) break; }
      len2=t2.hi-t2.lo+1;
      int len=extract(A); int n; int r=rest_off(A,len,&n); unsigned long long h=hsh(A+r,len-r,st)^((unsigned long long)(n%Q)<<50);
      if(h!=hs[i]){ mism++; int n2; for(int j=0;j<len2;j++) A[j]= SIDE==0? tm_get(&t2,t2.lo+j): tm_get(&t2,t2.hi-j); int r2=rest_off(A,len2,&n2);
        printf("event at trigger %lld: true n=%d rest=%d (reset run had rest %d)\n",i,n2,len2-r2,len-r); len=len2; s2=s2; st=s2; }
      len=shrink(A,len,B); load(B,len,st); }
    printf("mismatches %lld\n",mism);
    printf("reset run agrees on all %lld triggers\n",cnt); return 0; }
  // Brent
  long long power=1,lam=1; int plen; int r=run_to_trigger(1LL<<40); plen=extract(P); plen=shrink(P,plen,B); memcpy(P,B,plen); int pst=st; load(P,plen,pst);
  long long sw=0;
  while(sw<MAXS){
    r=run_to_trigger(1LL<<40); sw++;
    if(r==0){printf("HALTS after %lld sweeps (reset steps %lld)\n",sw,steps);return 0;}
    int len=extract(A); if(getenv("PFROM") && sw>=atoll(getenv("PFROM")) && sw<=atoll(getenv("PTO")) && sw%atoll(getenv("PEV"))==0){ printf("%lld ",sw); for(int j=0;j<len;j++) printf("%d^1 ",A[j]); printf("\n"); }
    if(getenv("FRONT")){ int len0=len; static unsigned char pr[1<<20]; static int pl=0; static long long fr=-1, nextp=1; int EX=getenv("EXCL")?atoi(getenv("EXCL")):0;
      int len=0; for(int q=0;q<len0;q++) if(A[q]) len=q+1;
      if(pl){ int mn=len<pl?len:pl; for(int j=EX;j<mn;j++) if(A[len-1-j]!=pr[pl-1-j]) { if(fr<0||j<fr) fr=j; break; } }
      memcpy(pr,A,len); pl=len; if(sw==nextp){ printf("front sweep %lld: closest change to the fixed end %lld cells (config %d cells, last %d ignored)\n",sw,fr,len,EX); nextp*=2; } }
    len=shrink(A,len,B); load(B,len,st);
    { static int lastlen=-1; if(len!=lastlen){ printf("sweep %lld: reset length %d\n",sw,len); if(lastlen>=0 && getenv("STOPEV")) return 0; if(lastlen>=0 && len>lastlen+N0/2*WL){printf("BIG EVENT\n");return 0;} fflush(stdout); lastlen=len; } }
    if(len==plen && st==pst && !memcmp(B,P,len)){printf("CYCLE: period %lld sweeps, found at sweep %lld\n",lam,sw);return 0;}
    if(power==lam){ memcpy(P,B,len); plen=len; pst=st; power*=2; lam=0; }
    lam++;
    if((sw & (sw-1))==0 && sw>1000000) {fprintf(stderr,"sweep %lld len %d\n",sw,len);}
  }
  printf("no cycle in %lld sweeps; last len %d\n",sw,plen);
}
