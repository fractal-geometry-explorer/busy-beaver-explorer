// Left excursions from "E reads 1 0 0" (more than 200 cells from the left end): whether the head comes back
// right past the token (and how far left it went first) or goes on to the left end; one excursion is followed at a time. usage: ./excursions STEPS
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define T 4000000
static unsigned char tape[T], snap[T]; static int first[T];
char tokat(long q,long*nq){ int x=0,y=0; while(snap[q]==1){x++;q++;} while(snap[q]==0&&y<3){y++;q++;} *nq=q; return x==1&&y==1?'x': x==2&&y==1?'y': x==1&&y==2?'u': x==2&&y==2?'v': '?'; }
int main(int argc,char**argv){
  char *m="1RB0LD_1RC0RD_1LA0RC_1RE1LB_1LF0LA_---0LE"; long N=atol(argv[1]);
  int w[6][2],d[6][2],n[6][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*x=m+7*s+3*b; if(x[0]=='-'){n[s][b]=-1;continue;} w[s][b]=x[0]-'0'; d[s][b]=x[1]=='R'?1:-1; n[s][b]=x[2]-'A';}
  long p=T/2,lo=p,hi=p,mx=p,last=0; int s=0; long cyc=0;
  for(long q=0;q<T;q++) first[q]=-1;
  long evp=-1, evend=0, evmin=0, evt=0; static long hist[2][64];
  for(long i=0;i<N;i++){int b=tape[p]; if(n[s][b]<0){printf("HALT %ld\n",i);return 0;}
    if(first[p]<0){ first[p]=s; if(evp<0 && cyc>100 && s==4 && snap[p]==1&&snap[p-1]==0 && p>lo+200){ long nq; char t=tokat(p,&nq); if(t=='u'){ evp=p; evend=nq; evmin=p; evt=i; } } }
    if(evp>=0){ if(p<evmin) evmin=p; if(p>=evend){ int dd=(evp-evmin)/10; if(dd>63)dd=63; hist[1][dd]++; evp=-1; } else if(p<evp-1500){ hist[0][63]++; evp=-1; } }
    tape[p]=w[s][b]; p+=d[s][b]; s=n[s][b];
    if(p>mx){mx=p;} if(p>hi)hi=p;
    if(p<lo){ if(i-last>200){ if(evp>=0){ hist[0][0]++; evp=-1;} memcpy(snap+lo-10,tape+lo-10,hi-lo+20); for(long q=lo-10;q<=hi+10;q++) first[q]=-1; cyc++; mx=p;} lo=p; last=i;}
  }
  printf("continue: excursion depth (cells/10) histogram\n"); for(int k=0;k<64;k++) if(hist[1][k]) printf("%d:%ld ",k*10,hist[1][k]); printf("\nturns(>1500 left or end): %ld %ld\n",hist[0][63],hist[0][0]);
}
