/* passtimes: the sweeps at which events enter the old zone, exact, for the four F08 machines (see window.c).
 *
 *   passtimes STATE M
 *
 * As window.c, but every event carries the number of its sweep, counted from the state (0 = the first sweep
 * after it): W_0 = sweeps 0, 1, 2; the second pass of a cell adds the window length to the numbers.  Prints, for
 * the window 3*2^D of the cut after M cells (D <= 61, so that sweep numbers fit in 64 bits; M = 129 gives
 * D = 60 for the machines with the new zone of 79 cells), every event that enters the old zone with its sweep.
 * Build: gcc -O2 -o passtimes passtimes.c */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef struct { uint64_t t; unsigned char e; } ev;
static unsigned char Z[1<<20];
static inline unsigned char cell(unsigned char *x, unsigned char e){
  if(e==0){*x^=1;return 3;} if(e==1) return *x?2:0; unsigned char o=*x?2:1; *x^=1; return o;}
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); unsigned long long t,n; long rl; if(fscanf(f,"%llu %llu %ld ",&t,&n,&rl)!=3) return 2;
  long L=0; int ch; while((ch=fgetc(f))=='0'||ch=='1') Z[L++]=ch-'0';
  long M=atol(argv[2]); long A=0,B=0;
  for(long i=0;i<L;){ long j=i; while(j+3<L&&Z[j+3]==Z[j]) j++; if(j+3-i>B-A){A=i;B=j+3;} i=j+1; }
  long CAP=atol(getenv("CAP")?getenv("CAP"):"300000000");
  ev *W=malloc(CAP*sizeof(ev)),*W2=malloc(CAP*sizeof(ev)); long N=3; uint64_t P=3; int D=0;
  for(int i=0;i<3;i++){W[i].e=((n+i)%3!=2)?2:1; W[i].t=i;}
  for(long m=0;m<M;m++){ unsigned char x0=Z[m],x=x0; long K=0; int r=0;
    do{ for(long i=0;i<N;i++){unsigned char e=cell(&x,W[i].e); if(e!=3){ if(K>=CAP){puts("CAP");return 1;} W2[K].e=e; W2[K].t=W[i].t+r*P; K++;}} r++; }while(x!=x0);
    if(r>1){P*=2;D++;}
    ev*tp=W;W=W2;W2=tp;N=K; }
  for(long m=M;m<L;m++){ unsigned char x=Z[m]; long K=0;
    for(long i=0;i<N;i++){unsigned char e=cell(&x,W[i].e); if(e!=3){W2[K]=W[i];W2[K].e=e;K++;}}
    ev*tp=W;W=W2;W2=tp;N=K;
    if(m+1==B){ printf("window 3*2^%d: %ld events enter the old zone (cut %ld); k, sweep number, event:\n",D,N,B);
      for(long i=0;i<N;i++) printf("%ld %llu %c\n",i+1,(unsigned long long)W[i].t,"F01"[W[i].e]); } }
  printf("leaving the word: %ld\n",N); return 0; }
