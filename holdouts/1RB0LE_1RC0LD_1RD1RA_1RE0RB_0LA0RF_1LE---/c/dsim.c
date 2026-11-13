// Digit-level simulator of the counter: the sweep rules proved in lean/Sweep.lean and lean/Carry.lean (the same
// cases as `nextR` in lean/Rle.lean), on digits run-length coded, so that a sweep costs time in the number of runs
// it changes, not in the number of digits.  It stops at the first sweep the proved rules do not cover (a carry at a
// leftmost block whose length is not 3 or 6j+9: the start of a nested run; or the other phase of the right end with
// a last digit that is not 1), printing the macro state there, and prints a line at every sweep where the left end
// changes.  Step counts are exact (unsigned 64-bit, so MAXSTEPS at most 1.8e19).
// usage: dsim R PHASE DIGITS START_STEP MAXSTEPS [REPORT_EVERY_SWEEPS]      (gcc -O2 -o dsim dsim.c)
//   R: the leftmost block 1^R;  PHASE: 0 for `0 1 B>0` at the right end (P), 1 for `0 1^4 B>0` (Q);
//   DIGITS: comma-separated, left to right;  START_STEP: the step count of that configuration.
// Examples (README, section Reproduce): the run from the first sweep configuration, and from the end of the first
// nested run.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned long long u64;
typedef struct { long long d; u64 c; } R;
R *D; long n=0, cap=1<<26;
static void push(long long d,u64 c){ if(!c) return; if(n>0&&D[n-1].d==d) D[n-1].c+=c; else { D[n].d=d; D[n].c=c; n++; if(n>=cap){fprintf(stderr,"cap\n");exit(1);} } }
R *K; long nk=0; // the odd suffix as runs of k (digit 2k+1), rightmost run first
static void dump(long long r,int ph,u64 t,u64 sw){
  printf("sweep %llu step %llu r=%lld ph=%d runs=%ld :",sw,t,r,ph,n);
  long lim = n<60? n:60;
  for(long i=0;i<lim;i++){ if(D[i].c==1) printf(" %lld",D[i].d); else printf(" %lld^%llu",D[i].d,D[i].c);} if(n>lim) printf(" ...(+%ld runs)",n-lim);
  printf("\n"); fflush(stdout);
}
int main(int argc,char**argv){
  long long r=atoll(argv[1]); int ph=atoi(argv[2]); u64 t=strtoull(argv[4],0,10); double mx=atof(argv[5]); u64 MAX=(u64)mx;
  u64 every= argc>6? strtoull(argv[6],0,10):0;
  D=malloc(sizeof(R)*cap); K=malloc(sizeof(R)*cap);
  { char*s=strdup(argv[3]); for(char*p=strtok(s,",");p;p=strtok(0,",")) push(atoll(p),1); }
  u64 sw=0;
  while(t<MAX){
    if(ph){ // Q phase: last digit 1 -> 2 0
      if(n==0||D[n-1].d!=1){ printf("UNCOVERED Q\n"); dump(r,ph,t,sw); return 0; }
      D[n-1].c--; if(!D[n-1].c) n--; push(2,1); push(0,1); t+=25; ph=0; sw++; continue;
    }
    // collect odd suffix
    nk=0; u64 cost=0;
    while(n>0 && (D[n-1].d&1)){ K[nk].d=D[n-1].d/2; K[nk].c=D[n-1].c; cost+= (20*(u64)K[nk].d+16)*D[n-1].c; nk++; n--; }
    // K is reversed (rightmost first); iterate from nk-1 down to 0 for left->right order
    if(n>0){
      long long b=D[n-1].d; D[n-1].c--; if(!D[n-1].c) n--;
      if(n>0){
        long long a=D[n-1].d; D[n-1].c--; if(!D[n-1].c) n--;
        if(b==0){ push(a+2,1);
          // then for each odd: 0^(2k) 1   (stepD with c=a+1: first group 0^(2k1) directly after a+2, then 1, ...)
          for(long i=nk-1;i>=0;i--){ long long k=K[i].d; u64 c=K[i].c; if(k==0) push(1,c); else for(u64 j=0;j<c;j++){ push(0,2*k); push(1,1);} }
          t+=21+cost;
        } else { push(a+1,1); push(0,b-1); push(1,1);
          for(long i=nk-1;i>=0;i--){ long long k=K[i].d; u64 c=K[i].c; if(k==0) push(1,c); else for(u64 j=0;j<c;j++){ push(0,2*k); push(1,1);} }
          t+=21+10*(u64)b+cost;
        }
      } else { // stop digit is the first digit: merges into raw
        if(b==0){ r+=6;
          // rawD ks = 0^(2k1) 1 0^(2k2) 1 ... 1  (empty if no odds)
          for(long i=nk-1;i>=0;i--){ long long k=K[i].d; u64 c=K[i].c; if(k==0) push(1,c); else for(u64 j=0;j<c;j++){ push(0,2*k); push(1,1);} }
          t+=21+cost;
        } else { r+=3; push(0,b-1); push(1,1);
          for(long i=nk-1;i>=0;i--){ long long k=K[i].d; u64 c=K[i].c; if(k==0) push(1,c); else for(u64 j=0;j<c;j++){ push(0,2*k); push(1,1);} }
          t+=21+10*(u64)b+cost;
        }
        printf("LEFT merge (first digit %lld): r -> %lld\n",b,r); dump(r,ph,t,sw+1);
      }
    } else { // all odd: carry at the left end
      if(nk==0){ printf("UNCOVERED empty\n"); return 0; }
      if(r==3){
        // first digit 2k1+1 -> 0^(2k1+2), then for the others: 1 0^(2k) ..., final 1
        long i=nk-1; long long k1=K[i].d; K[i].c--; push(0,2*k1+2); u64 add=59+20*(u64)k1; cost-= (20*(u64)k1+16);
        // remaining: stepD (zeros) 0 ks' = ... 1, 0^(2k2), 1, ... wait: E ++ [1] ++ 0^(2k) per k, then final 1
        for(;i>=0;i--){ long long k=K[i].d; u64 c=K[i].c; for(u64 j=0;j<c && k>0;j++){ push(1,1); push(0,2*k);} if(k==0) push(1,c); }
        push(1,1);
        t+=add+cost;
        printf("LEFT carry3\n"); dump(r,ph,t,sw+1);
      } else if(r%6==3 && r>=9){
        long long j=(r-9)/6; r=3; push(0,2*j+3);
        for(long i=nk-1;i>=0;i--){ long long k=K[i].d; u64 c=K[i].c; for(u64 jj=0;jj<c && k>0;jj++){ push(1,1); push(0,2*k);} if(k==0) push(1,c); }
        push(1,1);
        t+=103+20*(u64)j+cost;
        printf("LEFT carry9\n"); dump(r,ph,t,sw+1);
      } else {
        // restore and stop
        for(long i=nk-1;i>=0;i--) push(2*K[i].d+1,K[i].c);
        printf("NESTED (carry at r=%lld)\n",r); dump(r,ph,t,sw); return 0;
      }
    }
    sw++;
    if(every && sw%every==0) dump(r,ph,t,sw);
  }
  dump(r,ph,t,sw);
  return 0;
}
