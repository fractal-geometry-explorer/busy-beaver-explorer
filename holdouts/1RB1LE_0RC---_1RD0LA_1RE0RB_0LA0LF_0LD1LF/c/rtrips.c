/* rtrips N [ONLYLEFT]: direct simulation of 1RB1LE_0RC---_1RD0LA_1RE0RB_0LA0LF_0LD1LF from blank tape for N steps.
 * Prints a line at every R-instant (the head arrives at the right end: two cells from the end, after having been
 * more than 30 cells away) and at every L-instant (state E on the leftmost visited cell):
 *   R|L STEP STATE H-LO HI-H: g0 n1 g1 n2 ... gk
 * the tape from the leftmost visited cell to the rightmost, cut into maximal runs of the word 100 (counts n) and the
 * cells between them (g, '-' when empty).  With ONLYLEFT=1 only L lines and the R line right after each.
 * Used by py/odometer/validate.py to check the macro. */
#include <stdio.h>
#include <stdlib.h>
static const int W[6][2]={{1,1},{0,0},{1,0},{1,0},{0,0},{0,1}};
static const int M[6][2]={{1,-1},{1,0},{1,-1},{1,1},{-1,-1},{-1,-1}};
static const int S[6][2]={{1,4},{2,-1},{3,0},{4,1},{0,5},{3,5}};
#define SZ (1L<<30)
static unsigned char *t;
static void dump(char k,long long step,int s,long h,long lo,long hi){
  printf("%c %lld %c %ld %ld:",k,step,'A'+s,h-lo,hi-h);
  long i=lo; char g[64]; int gl=0;
  while(i<=hi){
    if(i+2<=hi && t[i]==1&&t[i+1]==0&&t[i+2]==0){ long n=0; while(i+2<=hi&&t[i]==1&&t[i+1]==0&&t[i+2]==0){n++;i+=3;}
      g[gl]=0; printf(" %s %ld",gl?g:"-",n); gl=0; continue;}
    if(gl<60) g[gl++]='0'+t[i]; i++;
  }
  g[gl]=0; printf(" %s\n",gl?g:"-");
}
int main(int argc,char**argv){
  long long N=atoll(argv[1]); int only=argc>2&&atoi(argv[2]);
  t=calloc(SZ,1); long h=SZ/2,lo=h,hi=h; int s=0,dir=1,pend=0;
  for(long long st=0;st<N;st++){
    int c=t[h];
    if(s==4&&h<=lo){ dump('L',st,s,h,lo,hi); pend=1; }
    if(S[s][c]<0){ printf("HALT %lld\n",st); return 0; }
    t[h]=W[s][c]; h+=M[s][c]; s=S[s][c]; if(h<lo)lo=h; if(h>hi)hi=h;
    if(h<=1||h>=SZ-2){ printf("TAPE %lld\n",st); return 1; }
    if(h>=hi-1 && dir==1){ if(!only||pend) dump('R',st+1,s,h,lo,hi); pend=0; dir=-1; }
    if(h<hi-30) dir=1;
  }
  printf("END %lld\n",N); return 0;
}
