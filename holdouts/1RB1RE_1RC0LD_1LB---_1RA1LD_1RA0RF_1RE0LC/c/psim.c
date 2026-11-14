// Accelerated exact simulator of 1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC on pairs of cells (tab.h, from py/pairs.py).
// The two stacks hold pairs (0='01' 1='11' 2='10' 3='00') and runs of the block word: (0011)^n on the left,
// (1aab)^n on the right. Two shift rules cross a run at once (Lean: sweep_left, sweep_right in lean/Rules.lean):
//     (0011)^n <D        ->  <D (1aab)^n             38 steps a word
//     001 B> (1aab)^n    ->  (1001)^n 001 B>         26 steps a word
// Everything else is one macro move at a time. A round ends when E reaches the blank at the right end.
// usage: psim ROUNDS [accel=1] [dumpfile]     (accel=0: no shift rules; the step counts must agree)
// Prints, at powers of two of rounds: steps, block length k, stack height, the lowest stack height touched since the
// last line (the frozen part of the region), the deepest round; at the end how often each macro move was used,
// what followed E> 1 and E> b, and the histogram of the depth of a round (pairs of the region read).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include "tab.h"
typedef unsigned __int128 u128;
#define CAP (1<<26)
static int32_t *Ls,*Lc,*Rs,*Rc; static long ln=0,rn=0; // cnt>0: run
static u128 steps=0; static long ev1[2][4],evb[4],evba[4],lastodd=-1,lastt0=-1; static long useR[6][4],useL[6][4];
static void pr128(u128 x){char b[50];int i=49;b[i]=0;if(!x)b[--i]='0';while(x){b[--i]='0'+(int)(x%10);x/=10;}fputs(b+i,stdout);}
static inline void pushL(int s){Ls[ln]=s;Lc[ln]=0;ln++;}
static inline void pushR(int s){Rs[rn]=s;Rc[rn]=0;rn++;}
int main(int argc,char**argv){
  long maxr=atol(argv[1]); int accel=argc>2?atoi(argv[2]):1;
  Ls=malloc(4L*CAP);Lc=malloc(4L*CAP);Rs=malloc(4L*CAP);Rc=malloc(4L*CAP);
  int st=0,dir=0; // start: state A in L form (head on second cell of the pair to the left)
  long round=0,nextp=1; long minh=1L<<60, minall=1L<<60; long h0=0; long maxdepth=0; long unacc=0;
  u128 c1=0,c2=0; // per-word costs, measured on first use
  long kblock=0; long hist[64];memset(hist,0,sizeof hist); long roundmin=0;
  for(;;){
    if(dir==0){ // moving left
      int x;
      if(ln==0){x=3; }
      else if(Lc[ln-1]>0){
        if(st==3&&accel){ // S1: (0011)^n <D -> <D (1aab)^n, 38 raw steps per word
          long n=Lc[ln-1]; ln--; steps+=(u128)n*38;
          if(rn>0&&Rc[rn-1]>0) Rc[rn-1]+=n; else {Rs[rn]=9;Rc[rn]=n;rn++;}
          if(ln<minh)minh=ln; continue;
        }
        if(--Lc[ln-1]==0)ln--; pushL(0);pushL(0);pushL(1);pushL(1); x=Ls[--ln];
      } else x=Ls[--ln];
      if(ln<minh)minh=ln;
      useL[st][x]++; const int*t=LL[st][x];
      if(!((st==3||st==1)&&x<2)) lastodd=round; if(t[0]<0){printf("HALT L st=%c x=%d round=%ld steps>=",'A'+st,x,round);pr128(steps);printf(" ln=%ld rn=%ld\n",ln,rn);return 0;}
      steps+=t[3]; if(t[1])pushL(t[0]);else pushR(t[0]); dir=t[1]; st=t[2]; unacc++;
    } else {
      int x;
      if(rn==0){
        x=3;
        if(st==4){ // round boundary
          round++;
          long depth=h0-minh; int b=0; while((1L<<b)<=depth&&b<62)b++; hist[b]++; if(depth>maxdepth)maxdepth=depth;
          if(minh<minall)minall=minh;
          { long n=0; for(;;){ if(ln>=4&&Lc[ln-1]==0&&Lc[ln-2]==0&&Lc[ln-3]==0&&Lc[ln-4]==0&&Ls[ln-1]==1&&Ls[ln-2]==1&&Ls[ln-3]==0&&Ls[ln-4]==0){ln-=4;n++;} else if(ln>0&&Lc[ln-1]>0){n+=Lc[ln-1];ln--;} else break; }
            if(n){Ls[ln]=8;Lc[ln]=n;ln++;} kblock=n; }
          if(round==nextp){printf("round %ld steps ",round);pr128(steps);printf(" k=%ld",kblock);printf(" ln=%ld minh(interval)=%ld maxdepth=%ld pairsteps=%ld\n",ln,minall,maxdepth,unacc);fflush(stdout);nextp*=2;minall=1L<<60;maxdepth=0;}
          if(round>=maxr){printf("end: round %ld steps ",round);pr128(steps);printf(" k=%ld region=%ld pairs\n",kblock,ln-1);break;}
          h0=ln; minh=ln;
        }
      } else if(Rc[rn-1]>0){
        if(st==1&&accel&&ln>=3&&Lc[ln-1]==0&&Lc[ln-2]==0&&Lc[ln-3]==0&&Ls[ln-1]==1&&Ls[ln-2]==0&&Ls[ln-3]==0){
          // S2: 001 B> (1aab)^n -> (1001)^n 001 B>  =  1 (0011)^(n-1) 001 001 B>
          long n=Rc[rn-1]; rn--; ln-=3; if(ln<minh)minh=ln;
          pushL(1); if(n>1){Ls[ln]=8;Lc[ln]=n-1;ln++;}
          pushL(0);pushL(0);pushL(1);pushL(0);pushL(0);pushL(1); steps+=(u128)n*26; continue;
        }
        if(--Rc[rn-1]==0)rn--; pushR(3);pushR(2);pushR(2);pushR(1); x=Rs[--rn];
      } else x=Rs[--rn];
      useR[st][x]++; const int*t=RR[st][x];
      if(!(st==4||st==1)) lastodd=round;
      if(st==4&&(x==1||x==3)){ int nx= rn>0? (Rc[rn-1]>0?1:Rs[rn-1]) : 3; int nn= (rn>1&&Rc[rn-1]==0)? (Rc[rn-2]>0?1:Rs[rn-2]) : 9; int tl= ln>0?(Lc[ln-1]>0?1:Ls[ln-1]):3;
        if(x==1){ ev1[tl&1][nx]++; if(!(tl&1)&&(nx==0||nx==3)) lastt0=round; } else { evb[nx]++; if(nx==2&&nn<4) evba[nn]++; } } if(t[0]<0){printf("HALT R st=%c x=%d round=%ld steps>=",'A'+st,x,round);pr128(steps);printf(" ln=%ld rn=%ld\n",ln,rn);return 0;}
      steps+=t[3]; if(t[1])pushL(t[0]);else pushR(t[0]); dir=t[1]; st=t[2]; unacc++;
    }
    if(ln>CAP-8||rn>CAP-8){printf("overflow\n");return 1;}
  }
  for(int a=0;a<6;a++){printf("%c> :",'A'+a);for(int x=0;x<4;x++)printf(" %ld",useR[a][x]);printf("   <%c :",'A'+a);for(int x=0;x<4;x++)printf(" %ld",useL[a][x]);printf("\n");}
  if(argc>3){FILE*f=fopen(argv[3],"w");for(long i=0;i<ln;i++){if(Lc[i]>0)fprintf(f,"(%d)",Lc[i]);else fputc("01ab"[Ls[i]],f);}fclose(f);}
  printf("E>1 next: t=0: %ld %ld %ld %ld ; t=1: %ld %ld %ld %ld\nE>b next: %ld %ld %ld %ld ; E>ba next: %ld %ld %ld %ld\n",ev1[0][0],ev1[0][1],ev1[0][2],ev1[0][3],ev1[1][0],ev1[1][1],ev1[1][2],ev1[1][3],evb[0],evb[1],evb[2],evb[3],evba[0],evba[1],evba[2],evba[3]);
  printf("last round with a move outside the D/E/B system: %ld; last round with 0 E> 1 followed by 0 or b: %ld\n",lastodd,lastt0);
  printf("depth histogram (log2 bins):");for(int b=0;b<40;b++)if(hist[b])printf(" %d:%ld",b,hist[b]);printf("\n");
  return 0;
}
