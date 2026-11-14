/* rvis MACHINE SIDE STATE PREFIX WORD N0 Q T0 VISITS OUTCELLS
 * A trigger is a step at which the head extends the tape on SIDE (L/R) in STATE; the cells from the head towards the
 * fixed end are then  c0 PREFIX WORD^n R.  The true run goes to trigger T0; from there the block is cut to
 * N0 + (n-N0) mod Q words at every trigger (as c/resetsim.c).  At each trigger: the trigger number, n mod Q, the depth
 * (how far into R the head went since the last trigger, in cells), the length of R and its first OUTCELLS cells.
 * PREFIX "-" = empty.  Stops with a message at a halt. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define CAP (1<<26)
static int Wr[6][2],Dr[6][2],Sr[6][2];
static unsigned char *tp; static long head,lo,hi; static int st;
int main(int c,char**v){ const char*m=v[1];
 for(int i=0;i<6;i++)for(int b=0;b<2;b++){const char*t=m+7*i+3*b; if(t[0]=='-')Sr[i][b]=-1; else {Wr[i][b]=t[0]-'0';Dr[i][b]=t[1]=='R'?1:-1;Sr[i][b]=t[2]-'A';}}
 int side=v[2][0]=='R'?1:-1; int S0=v[3][0]-'A'; const char*PF=v[4]; if(PF[0]=='-')PF=""; const char*WD=v[5]; int PL=strlen(PF),WL=strlen(WD);
 int N0=atoi(v[6]),Q=atoi(v[7]); long T0=atol(v[8]),NV=atol(v[9]); int OC=atoi(v[10]);
 tp=calloc(CAP,1); head=lo=hi=CAP/2; st=0; long trig=0; long ext=0; long rs=-1; unsigned long long k=0;
 static unsigned char buf[1<<24];
 for(;;){ int y=tp[head]; int ns=Sr[st][y]; if(ns<0){printf("HALT after trigger %ld (step %llu of this run)\n",trig,k+1);return 0;}
   tp[head]=Wr[st][y]; head+=Dr[st][y]; st=ns; k++;
   int t=0; if(head>hi){hi=head; if(side==1&&st==S0)t=1;} if(head<lo){lo=head; if(side==-1&&st==S0)t=1;}
   if(rs>=0){ long e= side==-1? head-rs : rs-head; if(e>ext)ext=e; }
   if(head<=2||head>=CAP-3){printf("tape overflow\n");return 1;}
   if(t){ trig++;
     // parse: cells from head towards the fixed end
     long q=head-side; int ok=1; for(int j=0;j<PL;j++) if(tp[q-side*j]!=PF[j]-'0') ok=0;
     long n=0; if(ok){ q-=side*PL; for(;;){ int mm=1; for(int j=0;j<WL;j++){ long p=q-side*j; if(p<lo||p>hi||tp[p]!=WD[j]-'0'){mm=0;break;} } if(!mm)break; q-=side*WL; n++; } }
     long far= side==-1? hi: lo; long rlen= side==-1? far-q+1 : q-far+1; if(rlen<0)rlen=0;
     if(trig>=T0){ if(trig>T0){ printf("%ld %ld %ld %ld ",trig,ok?n%Q:-1,ext,rlen); for(int j=0;j<OC&&j<rlen;j++)putchar(48+tp[q-side*j]); if(getenv("TAIL")){ int tl=atoi(getenv("TAIL")); putchar(32); for(long j=rlen>tl?rlen-tl:0;j<rlen;j++)putchar(48+tp[q-side*j]); } putchar(10); }
       if(ok && n>=N0){ long n2=N0+((n-N0)%Q); long d=(n-n2)*WL; if(d>0){ // remove d cells of block next to the prefix: shift the growing-end part towards the fixed end
           // cells: head, prefix, block(n words), R... ; keep R in place: move head+prefix+first n2 words by d towards the fixed end
           long keep=1+PL+n2*WL; for(long j=keep-1;j>=0;j--){ tp[head-side*(j+d)]=tp[head-side*j]; }
           for(long j=0;j<d;j++) tp[head-side*j]=0; head-=side*d; if(side==-1)lo=head; else hi=head; } }
       rs=q; }
     ext=0; if(trig>=T0+NV) return 0; } }
}
