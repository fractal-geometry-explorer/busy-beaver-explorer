// Step-count bounds for the visit-law run: the pass of VisitCheck.lean (`scan`), in place, with visit counts
// accumulated per rule type as (mantissa, exponent).  usage: steps STATEFILE(s_161210.txt)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#define SZ 3000000
static unsigned char buf[SZ]; static long lo, hi; // word = buf[lo..hi)
typedef struct { long double m; long x; } acc;   // m * 2^x
static void add(acc*a, long e, long double mt){ // add mt * 2^e
  if(mt==0) return;
  if(e>a->x){ long d=e-a->x; a->m = d>16000? 0 : ldexpl(a->m,-(int)d); a->x=e; }
  long d=a->x-e; if(d>16000) return; a->m += ldexpl(mt,-(int)d);
}
static acc Z0,HH,GG,LL, hZ0,hH,hG,hL;  // completed rounds; halting round (full counts, upper bound only)
static long maxe=0, maxc=0, nsteps=0, emax_round[4];
// one pass; returns 1 if it meets 1011 with a positive count
static int pass(int halting){
  long e=0,c=0,i=lo; acc *z=halting?&hZ0:&Z0,*h=halting?&hH:&HH,*g=halting?&hG:&GG,*l=halting?&hL:&LL;
  for(;;){
    nsteps++;
    long double mt; long et;
    if(e<30){ long v=(1L<<e)-c; if(v<=0) break; mt=(long double)v; et=0; }
    else { if(c>=(1L<<30)){ fprintf(stderr,"c too big\n"); exit(3);} mt=1.0L-ldexpl((long double)c,-(int)(e>16000?16000:e)); et=e; }
    if(e>maxe) maxe=e; if(c>maxc) maxc=c;
    while(hi<i+4) buf[hi++]=0;
    int a=buf[i],b=buf[i+1],d=buf[i+2]; int odd= e==0?1:(int)(c&1);
    if(a==1&&b==0&&d==0){ // 100: H on visits 1,3,..; Z0 on 2,4,..
      add(h,et,mt/2); add(z,et,mt/2);
      buf[i]=!odd; c= e==0?c:c/2; e= e>0?e-1:0; i+=3;
    } else if(a==1&&b==1&&d==0){ // 110: G once, then 000
      add(g,0,1); add(h,et,mt/2); add(z,et,mt/2);
      buf[i]=!odd; buf[i+1]=0; c= e==0?c:c/2; e= e>0?e-1:0; i+=3;
    } else if(a==0&&b==0&&d==0){
      add(h,et,mt/2); add(z,et,mt/2);
      buf[i]=odd; c= e==0?1:(c+1)/2; e= e>0?e-1:0; i+=3;
    } else if(a==1&&b==0&&d==1){
      if(buf[i+3]==1){ return 1; }
      if(buf[i+4]==1&&buf[i+5]==1&&i+5<hi){ fprintf(stderr,"guard fails\n"); exit(3); }
      add(l,et,mt); e+=1; c*=2; i+=4;
    } else if(a==0){ add(z,0,1); buf[i]=1; c+=1; }
    else { fprintf(stderr,"no rule (111) at %ld\n",i-lo); exit(3); }
  }
  return 0;
}
static double lg2(acc a){ return a.m>0? (double)a.x+log2((double)a.m) : -1e300; }
int main(int argc,char**argv){
  lo=hi=SZ-1200000; buf[hi++]=1;
  long K=161210;
  for(long r=1;r<=K;r++){ lo-=2; buf[lo]=1; buf[lo+1]=0; if(pass(0)){ printf("unexpected halt in round %ld\n",r); return 1; }
    if(r%20000==0||r==K){ fprintf(stderr,"round %ld len %ld maxe %ld maxc %ld steps %ld\n",r,hi-lo,maxe,maxc,nsteps); } }
  // compare with the Lean boundary word
  if(argc>1){ FILE*f=fopen(argv[1],"r"); long len; static char hex[400000]; if(fscanf(f,"%ld %399999s",&len,hex)!=2) return 2; long n=strlen(hex),bad=0;
    for(long j=0;j<len;j++){ long hd=n-1-j/4; int v=0; if(hd>=0){ char ch=hex[hd]; v= ch<='9'?ch-'0':ch-'a'+10; } int bit=(v>>(j%4))&1; int cell= lo+j<hi? buf[lo+j]:0; if(bit!=cell) bad++; }
    long extra=0; for(long j=lo+len;j<hi;j++) if(buf[j]) extra++;
    printf("word after %ld rounds: len here %ld, Lean len %ld, mismatching cells %ld, ones beyond %ld\n",K,hi-lo,len,bad,extra); }
  long steps_done=nsteps, maxe_done=maxe;
  lo-=2; buf[lo]=1; buf[lo+1]=0; int h=pass(1);
  printf("halting round meets 1011: %d\n",h);
  printf("scan steps in completed rounds %ld, max e completed %ld, max e incl. halting round %ld, max c %ld\n",steps_done,maxe_done,maxe,maxc);
  printf("log2 visit counts, completed rounds: Z0 %.6f H %.6f G %.6f L %.6f\n",lg2(Z0),lg2(HH),lg2(GG),lg2(LL));
  printf("log2 visit counts, halting round (full): Z0 %.6f H %.6f G %.6f L %.6f\n",lg2(hZ0),lg2(hH),lg2(hG),lg2(hL));
  // common exponent output
  long X=LL.x; if(hL.x>X) X=hL.x;
  #define M(a) ((double)ldexpl((a).m,(int)((a).x-X<-16000?-16000:(a).x-X)))
  printf("X %ld  mantissas completed: Z0 %.9g H %.9g G %.9g L %.9g ; halting: Z0 %.9g H %.9g G %.9g L %.9g\n",X,M(Z0),M(HH),M(GG),M(LL),M(hZ0),M(hH),M(hG),M(hL));
  return 0;
}
