// m5fast: run 1RB1LC_1LA0RE_0LD---_1RE0LF_1RF0RD_1LD0LB from blank tape, jumping over rounds.
// Write s = 01100.  At each record of the head in D at the left end the tape right of the head cell is parsed as
//   (10)^A  [s (10)^D1 ... s (10)^Dk]  J
// and, where it fits, many rounds are replaced by their result with the exact step count:
//  * J = j (10)^y, k = 0 (junction in the first block): half_round_0/1 (Lean), A -> A+2, y -> y-1, j flips,
//    4A+10 (j = 0) or 4A+6 (j = 1) steps;
//  * J = s (10)^b j (10)^c (junction in a later block): mid_round_0/1 (Lean for k = 0, 1, 2), A -> A-1, b -> b+3,
//    c -> c-1, j flips, 4(A-2) + 4b + 38 (j = 0) or 34 (j = 1) steps, plus 4D_i + 20 for each block between (D_i >= 2);
//  * J = s (10)^L (1001100)^n 1 0^inf (no junction; L >= 2): tail_round (Lean for k = 0, 1, 2), A -> A-1, n -> n+1,
//    4(A-2) + 4L + 24n + 38 steps plus 4D_i + 20 for each block between.
// For k > 2 blocks between, the rules are the same pattern; that case is covered only by the validation.
// usage: m5fast MAXSTEPS_LOG10 [VALIDATE_LOG10]
//   with VALIDATE_LOG10 = v, runs the plain machine beside it and compares tape and state at every record in D on the
//   left (every jump included) up to 10^v steps.  Environment: SZ = tape size (default 2^31), DBG = n prints every
//   n-th record where no rule applies.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
static long SZ=1L<<31;
static unsigned char *t;
static int nw[6][2],mv[6][2],ns[6][2];
static void pr(u128 v){char b[50];int i=49;b[i]=0;if(!v){putchar('0');return;}while(v){b[--i]='0'+(int)(v%10);v/=10;}fputs(b+i,stdout);}
static long lo,hi,p; static int st; static u128 steps;
static long cnt10(long i,long*e){long n=0;while(t[i]==1&&t[i+1]==0){n++;i+=2;}*e=i;return n;}
static int issep(long i){return t[i]==0&&t[i+1]==1&&t[i+2]==1&&t[i+3]==0&&t[i+4]==0;}
static long writeblk(long j,long n){for(long w=0;w<n;w++){t[j++]=1;t[j++]=0;}return j;}
long long jumps=0, jumped=0;
// try to jump at a D record; returns 1 if jumped
static int tryjump(void){
  long i=p+1,e; long A=cnt10(i,&e); i=e;
  if(A<2) return 0;
  // junction directly?
  if(!issep(i)){
    int j=t[i]; if(!(t[i+1]==1&&t[i+2]==0)) return 0;
    long y=cnt10(i+1,&e); long end=e;
    // half rounds: y -> y-1 each, need y>=1 before each; leave y>=1
    long k=y-1; if(k<1) return 0;
    u128 s=0; long x=A; int jj=j;
    for(long r=0;r<k;r++){ s+= jj==0? 4*(u128)x+10 : 4*(u128)x+6; x+=2; jj^=1; }
    long np=p-2*k; if(np<1000) return -1;
    long q=np; t[q++]=0; q=writeblk(q,x); t[q++]=jj; q=writeblk(q,y-k); if(q!=end){printf("BUG1\n");exit(1);}
    p=np; lo=np; steps+=s; jumps++; jumped+=k; return 1;
  }
  // intermediate blocks
  long S=0; long nb=0;
  long sepstart=i;
  for(;;){
    if(!issep(i)) return 0;
    long b=cnt10(i+5,&e); long k2=e;
    if(issep(k2)){
      // tail: (10)^b with b>=3 is the last block (b-1) plus the first unit 10 01100 of (1001100)^n 1 0^inf
      if(b>=3){ long u=k2+5, n=1; while(t[u]==1&&t[u+1]==0&&issep(u+2)){n++;u+=7;}
        if(t[u]==1){ long v=u+1; int blank=1; for(long w=v;w<=hi;w++) if(t[w]){blank=0;break;}
          if(blank){ long L=b-1; long SL=S+4*L+20; long k=A-2; if(k<1) return 0;
            u128 s=0; long a=A; long nn=n;
            for(long r=0;r<k;r++){ s+=(u128)(4*(a-2)+SL+24*nn+18); a--; nn++; }
            long np=p-2*k; if(np<1000) return -1;
            long midlen=i-sepstart; long newsep=np+1+2*a;
            memmove(t+newsep,t+sepstart,midlen);
            long q=np; t[q++]=0; q=writeblk(q,a); q+=midlen; t[q++]=0;t[q++]=1;t[q++]=1;t[q++]=0;t[q++]=0;
            q=writeblk(q,L); for(long w=0;w<nn;w++){ t[q++]=1;t[q++]=0;t[q++]=0;t[q++]=1;t[q++]=1;t[q++]=0;t[q++]=0; }
            t[q++]=1; for(long w=q;w<=hi;w++) t[w]=0; if(q-1>hi) hi=q-1;
            p=np; lo=np; steps+=s; jumps++; jumped+=k; return 1; } } }
      if(b<2) return 0; S+=4*b+20; nb++; i=k2; continue; }
    int j=t[k2]; if(!(t[k2+1]==1&&t[k2+2]==0)) return 0;
    long c=cnt10(k2+1,&e); long end=e;
    long k=A-1; if(c<k) k=c; k-=1; if(k<1) return 0;  // keep one word spare on both sides
    u128 s=0; long a=A; long bb=b; int jj=j;
    for(long r=0;r<k;r++){ s+= (u128)(4*(a-2)+4*bb+(jj==0?38:34)+S); a--; bb+=3; jj^=1; }
    long np=p-2*k; if(np<1000) return -1;
    // rebuild: copy the intermediate region [sepstart, i) (unchanged) to its new place
    long midlen=i-sepstart; long newsep=np+1+2*a;
    memmove(t+newsep,t+sepstart,midlen);
    long q=np; t[q++]=0; q=writeblk(q,a); q+=midlen; t[q++]=0;t[q++]=1;t[q++]=1;t[q++]=0;t[q++]=0;
    q=writeblk(q,bb); t[q++]=jj; q=writeblk(q,c-k); if(q!=end){printf("BUG2 %ld %ld\n",q,end);exit(1);}
    p=np; lo=np; steps+=s; jumps++; jumped+=k; return 1;
  }
}
static long DBG=0, nf=0;
static unsigned char *t2; static long p2,hi2; static int st2; static u128 steps2; static u128 VAL=0; static long long checks=0;
static void validate(void){
  while(steps2<steps){ int r=t2[p2]; int n=ns[st2][r]; if(n<0){puts("VALIDATION: plain run halts");exit(1);}
    t2[p2]=nw[st2][r]; p2+=mv[st2][r]; st2=n; steps2++; if(p2>hi2) hi2=p2; }
  if(steps2!=steps||st2!=st){puts("VALIDATION FAIL: step/state");exit(1);}
  long e1=hi, e2=hi2; while(e1>p && !t[e1]) e1--; while(e2>p2 && !t2[e2]) e2--;
  if(e1-p!=e2-p2 || memcmp(t+p,t2+p2,e1-p+1)){printf("VALIDATION FAIL: tape at ");pr(steps);puts("");exit(1);}
  for(long q=1;q<64;q++) if(t2[p2-q]){puts("VALIDATION FAIL: left");exit(1);}
  checks++; }
static void dump(void){ printf("NOJUMP ");pr(steps);putchar(' '); long i=p+1; int out=0;
  static char buf[1<<22]; long bl=0; while(i<=hi && bl<(1<<22)-100){ long e; long n=cnt10(i,&e); if(n>=2){bl+=sprintf(buf+bl,"(10)^%ld ",n); i=e;} else if(issep(i)){bl+=sprintf(buf+bl,"S ");i+=5;} else {buf[bl++]='0'+t[i];i++;} }
  buf[bl]=0; if(bl>300){fwrite(buf,1,150,stdout);fputs(" ... ",stdout);fputs(buf+bl-300,stdout);} else fputs(buf,stdout); putchar('\n'); (void)out; }
int main(int argc,char**argv){ if(getenv("DBG")) DBG=atol(getenv("DBG"));
  const char*m="1RB1LC_1LA0RE_0LD---_1RE0LF_1RF0RD_1LD0LB";
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){const char*x=m+s*7+r*3; if(x[0]=='-'){ns[s][r]=-1;continue;} nw[s][r]=x[0]-'0'; mv[s][r]=x[1]=='R'?1:-1; ns[s][r]=x[2]-'A';}
  double L=atof(argv[1]); u128 MAX=1; for(int i=0;i<(int)L;i++) MAX*=10;
  if(getenv("SZ")) SZ=atol(getenv("SZ")); t=calloc(SZ,1); if(argc>2){ VAL=1; for(int i=0;i<atoi(argv[2]);i++) VAL*=10; t2=calloc(SZ,1); } p=SZ-(1L<<24); lo=hi=p; st=0; steps=0; p2=p; hi2=p; st2=0; steps2=0;
  u128 nextrep=1000;
  setvbuf(stdout,NULL,_IOLBF,0);
  while(steps<MAX){
    int r=t[p]; int n=ns[st][r]; if(n<0){printf("HALT steps ");pr(steps);printf("\n");return 0;}
    t[p]=nw[st][r]; p+=mv[st][r]; st=n; steps++;
    if(p>hi){hi=p; if(hi>SZ-100){puts("OUT R");return 1;}}
    if(p<lo){ lo=p; if(st==3){ int j=tryjump(); if(j<0){puts("OUT L");return 1;} if(j==0 && DBG && (++nf % DBG)==0) dump(); if(VAL && steps<VAL) validate(); else if(VAL){printf("validated %lld records to ",checks);pr(steps);puts("");return 0;} }
      if(steps>=nextrep){ printf("steps ");pr(steps);printf(" width %ld jumps %lld rounds-jumped %lld\n",hi-lo+1,jumps,jumped); nextrep*=10; }
    }
  }
  printf("done steps ");pr(steps);printf(" width %ld jumps %lld rounds-jumped %lld\n",hi-lo+1,jumps,jumped);
  return 0;}
