// m7fast: run 1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA, jumping over periods.
// At a record of the head in B at the left end with the tape  0^inf B> 0 0 1 (1100)^n (10110110)^m R  and m >= 5,
// the Lean rule `period` (lean/Rules.lean: (n, m+5) -> (n+31, m) in 448n+6952 steps, for every R; `periods` in
// lean/Periods.lean chains them) is applied floor(m/5) times at once, with the exact step count.  Everything else is
// simulated step by step.
// usage: m7fast MAXSTEPS_LOG10 [N M [T]]
//   from blank tape, or from  0^inf B> 0 0 1 (1100)^N (10110110)^M 1001 0^inf  (with T: ... 10 (1110)^T 1 0^inf).
//   Prints the phase ends (such records with m < 5) and the first record after each reset, with the tape after
//   the d block.  Environment: SZ = tape size in bytes (default 2^31); VAL = k also runs the plain machine beside it
//   and compares the whole tape and state at every record on the left (and after every jump) up to 10^k steps.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
static unsigned char *t; static long SZ=1L<<31;
static void pr(u128 v){char b[50];int i=49;b[i]=0;if(!v){putchar('0');return;}while(v){b[--i]='0'+(int)(v%10);v/=10;}fputs(b+i,stdout);}
static long HI;
static unsigned char *t2; static long p2,hi2; static int st2; static u128 steps2; static u128 VAL=0; static long long checks=0;
static int (*NS)[2],(*NW)[2],(*MV)[2];
static void validate(long p, int st, u128 steps, long hi){
  while(steps2<steps){ int r=t2[p2]; int n=NS[st2][r]; if(n<0){puts("VALIDATION: plain run halts");exit(1);}
    t2[p2]=NW[st2][r]; p2+=MV[st2][r]; st2=n; steps2++; if(p2>hi2) hi2=p2; }
  if(steps2!=steps||st2!=st){puts("VALIDATION FAIL: step/state");exit(1);}
  long e1=hi, e2=hi2; while(e1>p && !t[e1]) e1--; while(e2>p2 && !t2[e2]) e2--;
  if(e1-p!=e2-p2 || memcmp(t+p,t2+p2,e1-p+1)){printf("VALIDATION FAIL: tape at ");pr(steps);puts("");exit(1);}
  for(long q=1;q<64;q++) if(t2[p2-q]){puts("VALIDATION FAIL: left");exit(1);}
  checks++; }
static void tail(long i){ // the tape after the d block, as  word^k  runs of 1110, 1100, 10110110 and single cells
  long e=HI; while(e>i&&!t[e]) e--; int out=0;
  while(i<=e && out<200){ long k=0; while(i+3<=e && t[i]==1&&t[i+1]==1&&t[i+2]==1&&t[i+3]==0){k++;i+=4;}
    if(k){out+=printf("(1110)^%ld ",k);continue;} putchar('0'+t[i]); out++; i++; }
  putchar('\n'); }
int main(int argc,char**argv){
  const char*mm="1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA";
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){const char*x=mm+s*7+r*3; if(x[0]=='-'){ns[s][r]=-1;continue;} nw[s][r]=x[0]-'0'; mv[s][r]=x[1]=='R'?1:-1; ns[s][r]=x[2]-'A';}
  if(getenv("SZ")) SZ=atol(getenv("SZ"));
  int L=atoi(argv[1]); u128 MAX=1; for(int i=0;i<L;i++) MAX*=10;
  t=calloc(SZ,1); long p=SZ-(SZ/8), lo=p, hi=p; int st=0; u128 steps=0;
  NS=ns; NW=nw; MV=mv;
  if(getenv("VAL")){ VAL=1; for(int i=0;i<atoi(getenv("VAL"));i++) VAL*=10; t2=calloc(SZ,1); p2=p; hi2=p; st2=0; steps2=0; }
  if(argc>3){ long n=atol(argv[2]), m=atol(argv[3]); long q=p; t[q++]=0;t[q++]=0;t[q++]=1;
    for(long i=0;i<n;i++){t[q++]=1;t[q++]=1;t[q++]=0;t[q++]=0;} for(long i=0;i<m;i++){const char*d="10110110";for(int k=0;k<8;k++)t[q++]=d[k]-'0';}
    if(argc>4){ long tt=atol(argv[4]); t[q++]=1;t[q++]=0; for(long k=0;k<tt;k++){t[q++]=1;t[q++]=1;t[q++]=1;t[q++]=0;} t[q++]=1; }
    else { t[q++]=1;t[q++]=0;t[q++]=0;t[q++]=1; } hi=q-1; HI=hi; st=1; }
  setvbuf(stdout,NULL,_IOLBF,0); long long periods=0; int after=0;
  while(steps<MAX){
    int r=t[p]; int n=ns[st][r]; if(n<0){printf("HALT steps ");pr(steps);printf("\n");return 0;}
    t[p]=nw[st][r]; p+=mv[st][r]; st=n; steps++;
    if(p>hi){hi=p;HI=hi; if(hi>SZ-100){puts("OUT R");return 1;}}
    if(p<lo){ lo=p; if(p<100){puts("OUT L");return 1;}
      if(VAL){ if(steps<VAL) validate(p,st,steps,hi); else {printf("validated %lld records to ",checks);pr(steps);puts("");return 0;} }
      if(st==1 && t[p]==0&&t[p+1]==0&&t[p+2]==1){
        long i=p+3,nn=0; while(t[i]==1&&t[i+1]==1&&t[i+2]==0&&t[i+3]==0){nn++;i+=4;}
        long md=0; static const unsigned char D[8]={1,0,1,1,0,1,1,0};
        while(!memcmp(t+i,D,8)){md++;i+=8;}
        { {
            if(nn<1) goto skip;
            { int ok = md>0 || (t[i]==1&&t[i+1]==0&&t[i+2]==0&&t[i+3]==1) || (t[i]==1&&t[i+1]==0&&t[i+2]==1&&t[i+3]==1&&t[i+4]==1&&t[i+5]==0);
              if(!ok && md<5) goto skip; }
            if(after){ printf("after-reset steps ");pr(steps);printf(" n %ld m %ld ",nn,md); tail(i); after=0; }
            if(md>=5){ long q=md/5; u128 s=0; for(long k=0;k<q;k++) s+=448*(u128)(nn+31*k)+6952;
              long n2=nn+31*q, m2=md-5*q; long np=p-(4*(n2-nn)-8*(md-m2));  // tape grows by 84 cells a period, at the left
              if(np<100){puts("OUT L");return 1;}
              long w=np; t[w++]=0;t[w++]=0;t[w++]=1; for(long k=0;k<n2;k++){t[w++]=1;t[w++]=1;t[w++]=0;t[w++]=0;}
              for(long k=0;k<m2;k++) for(int z=0;z<8;z++) t[w++]=D[z];
              if(w!=i){printf("BUG %ld %ld\n",w,i);return 1;}
              p=np; lo=np; steps+=s; periods+=q; nn=n2; md=m2; if(VAL&&steps<VAL) validate(p,st,steps,hi); }
            printf("phase-end steps ");pr(steps);printf(" n %ld m %ld ",nn,md); tail(i); after=1; skip:;
          }}
      }}
  }
  printf("done steps ");pr(steps);printf(" periods %lld\n",periods);
  return 0;}
