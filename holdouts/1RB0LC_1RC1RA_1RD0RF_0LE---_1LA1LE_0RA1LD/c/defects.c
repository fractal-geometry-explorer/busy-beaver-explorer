/* defects.c: the pulse rules of 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD checked on the run from blank tape.
 *
 * usage: defects STEPS [K]
 *   At each visit of the head to the left end in the standard form  C>0 (011)^a 001101 ...  it lists the defects
 *   after 001101: runs of three or more 1s and runs of two or more 0s (the zeros at the end of the tape excluded),
 *   with the number of transparent words (runs of one or two 1s) before each. It predicts the list at the next such
 *   visit from the pulse rules (first defect 1^k: k >= 6 -> 1^(k-3); k = 4, 5 -> dissolves; k = 3 -> 00), and
 *   prints the first K visits where the prediction fails ("events"), then a summary: how many events had a run of 1s,
 *   00, 000 or longer zeros as first defect (an empty list means the pulse went to the end of the tape).
 * build: gcc -O2 -o defects defects.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// 1-runs of length >=3 (+k) and 0-runs of length >=2 (-j), the last 0-run (tape end) excluded.
// Checks the pulse calculus against the previous X visit; prints the visits where it fails ("events").
#define MX 2000000
static int pv[MX],cv[MX]; static int pw[MX],cw[MX]; long long first[10];
int main(int argc,char**argv){
 const char*m="1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD"; int W[6][2],D[6][2],N[6][2];
 for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*x=m+7*s+3*b; if(x[0]=='-'){N[s][b]=-1;continue;} W[s][b]=x[0]-'0';D[s][b]=x[1]=='R'?1:-1;N[s][b]=x[2]-'A';}
 long long to=atoll(argv[1]); int verb=argc>2?atoi(argv[2]):30;
 long long S=1LL<<27; unsigned char*t=calloc(S,1); long long p=S/2,lo=p,hi=p; int st=0;
 int np=-1,nc; long long nX=0,nev=0,lastX=0;
 for(long long k=1;k<=to;k++){ int b=t[p]; int ns=N[st][b]; if(ns<0){printf("HALT %lld\n",k);fflush(stdout);return 0;} t[p]=W[st][b]; p+=D[st][b]; st=ns;
  if(p<lo)lo=p; if(p>hi)hi=p;
  if(st==2&&p==lo){
    long long q=lo+1,a=0; while(q+2<=hi&&t[q]==0&&t[q+1]==1&&t[q+2]==1){a++;q+=3;}
    if(!(q+5<=hi&&t[q]==0&&t[q+1]==0&&t[q+2]==1&&t[q+3]==1&&t[q+4]==0&&t[q+5]==1)) continue;
    nX++; q+=6; // after 001101
    nc=0; int words=0; long long i=q;
    while(i<=hi){ int r=0; while(i<=hi&&t[i]){r++;i++;} long long z0=i; int z=0; while(i<=hi&&!t[i]){z++;i++;}
      if(r>=3){ cw[nc]=words; cv[nc++]=r; words=0; } else if(r>0) words++;
      if(z>=2 && i<=hi){ cw[nc]=words; cv[nc++]=-z; words=0; } }
    // predict
    int ok=0;
    if(np>=0){ static int ev[MX]; int ne=0,j=0;
            if(j<np){ if(pv[j]>=6) {ev[ne++]=pv[j]-3; j++;} else if(pv[j]==3){ev[ne++]=-2;j++;} else if(pv[j]==4||pv[j]==5){j++;} else j=-1; }
      else j=-1;
      if(j>=0){ for(;j<np;j++) ev[ne++]=pv[j]; ok = (ne==nc) && !memcmp(ev,cv,nc*sizeof(int)); }
    }
    if(!ok){ nev++; if(np>0&&cv[0]!=pv[0]) {} if(np>0) first[pv[0]<0? (pv[0]<-9?9:-pv[0]) : 0]++; if(nev<=verb){ printf("%lld X#%lld (+%lld) a=%lld len=%lld n=%d :",k,nX,k-lastX,a,hi-lo,nc); int lim=nc<40?nc:40; for(int j=0;j<lim;j++) printf(" [%d]%d",cw[j],cv[j]); if(nc>40) printf(" ..."); printf("\n"); fflush(stdout);} }
    memcpy(pv,cv,nc*sizeof(int)); np=nc; lastX=k;
  }
 } printf("done X visits %lld events %lld; first defect before event: fuse %lld, 0^2 %lld, 0^3 %lld, 0^4+ %lld/%lld/%lld\n",nX,nev,first[0],first[2],first[3],first[4],first[5],first[9]); return 0;}
