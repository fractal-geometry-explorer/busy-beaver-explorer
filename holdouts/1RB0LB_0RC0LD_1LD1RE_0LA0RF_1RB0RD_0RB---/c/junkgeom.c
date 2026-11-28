// junkgeom.c: how close a round comes to "junk after a digit" (the only way to a dangerous junk event).
//
// A junk event whose last block before the stop is a digit needs this geometry (G): the earlier round's last three
// blocks are digits B1 B2 B3, and the next round's blocks start on the last cell (a 0) of B1 and of B2. Then the next
// round takes one visit and halves in each (lean/Deficit.lean, junk_after_digit_count): it stops on the 0 before the
// old last 1 exactly when it enters B1's last cell with nX = 4..7 visits (6 or 7 is the dangerous count 3 after).
// This program runs the deficit pass (as c/deficit.c) and, in every round with G, records nX, the earlier round's
// counts m1 m2 m3 at B1 B2 B3, the gap nX - 2 m1 (lean/Deficit.lean, offset2_gap), and where the round stopped.
//
// usage: gcc -O2 -o junkgeom junkgeom.c && ./junkgeom ROUNDS
// output: one line "r... old m=m1,m2,m3 nX=.. gap .." for every round with G and nX < 10; then histograms of m1
// (with the gap nX - 2 m1 for each m1), of nX - 2 m1, and of nX with the stop position (old end minus stop cell,
// bins <=-6 .. >=2; junk is 2).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static uint8_t *T; static const long N=1L<<27;
#define KB 24
int main(int argc,char**argv){
  long R=atol(argv[1]); T=calloc(N,1); long F=N/8,E=F+1; T[F]=1;
  long op[KB]; char ok_[KB]; long onn[KB]; int on=0; long dh[200]={0}; long mh[64]={0}; static long J[64][40];             // old round's last blocks
  long hist[64]={0}; long hgap[64][8]={{0}}; long cond=0;
  for(long r=1;r<=R;r++){
    F-=2;T[F]=1;T[F+1]=0; long p=F,e=0,c=0,oldE=E;
    long bp[KB]; char bk[KB]; long bn[KB]; int nb=0; long zq=-1; long zn=0;
    for(;;){
      if(e<62&&c==(1L<<e))break;
      uint8_t*w=T+p;
      if(w[0]==0){ zq=p; zn=(e<62)?((1L<<e)-c):(1L<<40); w[0]=1;c++; continue;}
      char k=w[2]==0?'d':(w[1]==0&&w[3]==0)?'L':w[1]==0?'x':'!';
      long n=(e<62)?((1L<<e)-c):(1L<<40); if(zq==p) n=zn;
      bp[nb%KB]=p; bk[nb%KB]=k; bn[nb%KB]=n; nb++;
      if(k=='d'){w[0]=e==0?0:!(c&1);w[1]=0;if(e>0){e--;c/=2;}p+=3;}
      else if(k=='L'){e++;c*=2;p+=4;}
      else if(k=='x'){w[0]=0;w[2]=0;w[3]=1;c++;}
      else {printf("111 round %ld\n",r);return 0;}
    }
    long stop=p;
    if(p+4>E)E=p+4; while(E>F&&T[E-1]==0)E--;
    // condition on old blocks
    if(on>=3){
      long o1=op[(on-3)%KB],o2=op[(on-2)%KB],o3=op[(on-1)%KB];
      if(ok_[(on-3)%KB]=='d'&&ok_[(on-2)%KB]=='d'&&ok_[(on-1)%KB]=='d'){
        long nx=-1; int f2=0; long m1=onn[(on-3)%KB],m2=onn[(on-2)%KB],m3=onn[(on-1)%KB];
        for(int i=nb>KB?nb-KB:0;i<nb;i++){ if(bp[i%KB]==o1+2) nx=bn[i%KB]; if(bp[i%KB]==o2+2) f2=1; }
        if(nx>=0&&f2){ cond++; int b= nx<63?nx:63; hist[b]++; long g=oldE-stop; int gi=g<-6?0:g>1?7:(int)(g+7); if(gi<0)gi=0; if(gi>7)gi=7; hgap[b][gi]++; long df=nx-2*m1; if(df>-100&&df<100) dh[df+100]++; mh[m1<63?m1:63]++; if(df>=-20&&df<20) J[m1<63?m1:63][df+20]++; if(nx<10) printf("r%ld old m=%ld,%ld,%ld nX=%ld gap %ld\n",r,m1,m2,m3,nx,g); }
      }
    }
    on=0; for(int i=nb>KB?nb-KB:0;i<nb;i++){ op[on%KB]=bp[i%KB]; ok_[on%KB]=bk[i%KB]; onn[on%KB]=bn[i%KB]; on++; }
  }
  for(int i=0;i<64;i++) if(mh[i]){ printf("m1=%d: %ld  delta:",i,mh[i]); for(int d=0;d<40;d++) if(J[i][d]) printf(" %d:%ld",d-20,J[i][d]); printf("\n");}
  for(int i=0;i<200;i++) if(dh[i]) printf("nX-2m1=%d: %ld\n",i-100,dh[i]);
  printf("rounds %ld, condition met %ld\n",R,cond);
  for(int b=0;b<64;b++) if(hist[b]){ printf("nX=%d%s: %ld  gaps(<=-6..>=2):",b,b==63?"+":"",hist[b]); for(int g=0;g<8;g++)printf(" %ld",hgap[b][g]); printf("\n");}
}
