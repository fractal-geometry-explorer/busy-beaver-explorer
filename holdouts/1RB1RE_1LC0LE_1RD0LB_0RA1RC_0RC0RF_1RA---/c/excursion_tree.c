// Case tree of one "excursion" of a Turing machine, by direct simulation.
// Start: head in state A on a blank cell, everything to its right blank, everything to its left UNKNOWN.
// A left cell is fixed (0 and 1 are both tried) only when the head first reads it.  A branch ends when
//   EVENT: the head is in state A on a cell it never visited, right of everything visited (so again: A on blank, blank to
//          the right, and the left tape is some word: an instance of the start),
//   HALT:  the halting transition is taken,
//   DEEP:  the head wants to read more than N unknown cells (branch not decided),
//   LONG:  more than MAXSTEPS steps without any of these.
// If there are no HALT and no LONG leaves: every run from "any left tape, A on blank, blank right" that never reads
// more than N cells to the left of its starting cell between two events never halts.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define W 1024
typedef struct { unsigned char t[W]; int pos, lo, hi, st; long steps; } Cfg;
static int wr[6][2], mv[6][2], nx[6][2];
int main(int argc,char**argv){
  if(argc<3){fprintf(stderr,"usage: excursion_tree MACHINE N [MAXSTEPS]\n");return 2;}
  const char*m=argv[1]; int N=atoi(argv[2]); long maxsteps=argc>3?atol(argv[3]):100000000L;
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*p=m+s*7+b*3; if(p[0]=='-'){nx[s][b]=-1;continue;} wr[s][b]=p[0]-'0'; mv[s][b]=p[1]=='R'?1:-1; nx[s][b]=p[2]-'A';}
  Cfg*stack=malloc(sizeof(Cfg)*(N+4)); int sp=0;
  int P0=W/2;
  Cfg c; memset(&c,0,sizeof c); c.pos=P0; c.lo=P0; c.hi=P0; c.st=0; c.steps=0;
  unsigned long long ev=0,halt=0,deep=0,lng=0,nodes=0,total=0; long maxlen=0; int maxdepth=0;
  stack[sp++]=c;
  while(sp){
    c=stack[--sp];
    for(;;){
      if(c.pos<c.lo){
        if(P0-c.pos>N){deep++;break;}
        // branch: push the 1-branch, continue with 0
        c.lo=c.pos; if(P0-c.lo>maxdepth)maxdepth=P0-c.lo;
        Cfg d=c; d.t[d.pos]=1; stack[sp++]=d; nodes++;
        c.t[c.pos]=0;
      }
      if(c.pos>=c.hi){
        if(c.st==0&&c.steps>0){ev++; if(c.steps>maxlen)maxlen=c.steps; break;}
        c.hi=c.pos+1; if(c.hi>=W-2){fprintf(stderr,"tape overflow\n");return 1;}
      }
      int b=c.t[c.pos];
      if(nx[c.st][b]<0){halt++; printf("HALT after %ld steps, depth %d\n",c.steps,P0-c.lo); break;}
      c.t[c.pos]=wr[c.st][b]; int s2=nx[c.st][b]; c.pos+=mv[c.st][b]; c.st=s2; c.steps++; total++;
      if(c.steps>maxsteps){lng++;break;}
    }
  }
  printf("N=%d: EVENT %llu  HALT %llu  DEEP %llu  LONG %llu  (branch points %llu, deepest read %d, longest branch %ld steps, %llu steps in all)\n",N,ev,halt,deep,lng,nodes,maxdepth,maxlen,total);
  return (halt||lng)?1:0;
}
