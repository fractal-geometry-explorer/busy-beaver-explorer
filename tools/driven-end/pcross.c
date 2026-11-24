// pcross MACHINE (env DUMP=1: print the end's cells after each line, read outward; FIRST=1: cut after the leftmost run)
// pcross MACHINE STEPS ERASIDE(L|R) ENDSIDE(L|R) [MINLEN]
// era = head extends tape on ERASIDE. At era start: find maximal periodic runs (period p<=12, length >= MINLEN cells, >=4 periods)
// boundary: ENDSIDE=R -> cut right after the rightmost run; L -> cut right before the leftmost run.
// During the era log crossings of the cut (into end side: "X>", back: ">Y" as pairs X:Y ...). Print per era.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define T 40000000
int W[6][2],M[6][2],N[6][2];
unsigned char tape[T];
int main(int argc,char**argv){
  char*s=argv[1]; long steps=atol(argv[2]); int eside=argv[3][0]=='R'; int side=argv[4][0]=='R'; int minlen=argc>5?atoi(argv[5]):30;
  for(int q=0;q<6;q++)for(int b=0;b<2;b++){char*p=s+q*7+b*3; if(p[0]=='-'){N[q][b]=-1;continue;}
    W[q][b]=p[0]-'0'; M[q][b]=p[1]=='R'?1:-1; N[q][b]=p[2]-'A';}
  long pos=T/2,q=0,lo=pos,hi=pos,t; long cut=-1; long era=0;
  static char buf[1<<20]; int bl=0; int per=0; static char sd[1<<22];
  for(t=0;t<steps;t++){
    int b=tape[pos]; int nq=N[q][b]; if(nq<0){printf("HALT %ld pos-cut %ld\n",t,pos-cut);break;}
    tape[pos]=W[q][b]; long np=pos+M[q][b];
    if(cut>=0 && bl<(1<<20)-8){
      if(side){ if(pos==cut-1&&np==cut){buf[bl++]='A'+nq;} if(pos==cut&&np==cut-1){buf[bl++]='a'+nq;} }
      else { if(pos==cut&&np==cut-1){buf[bl++]='A'+nq;} if(pos==cut-1&&np==cut){buf[bl++]='a'+nq;} }
    }
    pos=np;q=nq;
    int ext=0; if(pos<lo){lo=pos; if(!eside)ext=1;} if(pos>hi){hi=pos; if(eside)ext=1;}
    if(ext){
      if(cut>=0 && bl){buf[bl]=0; printf("%ld %ld %ld %ld %d %s ",era,t,side?hi-cut:cut-lo,hi-lo,per,buf); if(!getenv("DUMP")){} else { printf("%s ",sd); if(side){for(long y=cut;y<=hi;y++)putchar(48+tape[y]);} else {for(long y=cut-1;y>=lo;y--)putchar(48+tape[y]);}} printf("\n");}
      era++; bl=0; cut=-1;
      // find runs: scan for periodic stretches
      long bestcut=-1;
      for(int p=1;p<=12;p++){
        long runstart=lo, x=lo;
        // run: maximal segments where tape[y]==tape[y+p]
        long y=lo; 
        while(y+p<=hi){
          long st=y; while(y+p<=hi && tape[y]==tape[y+p]) y++;
          long len=y-st+p; // segment [st, y+p)
          if(len>=minlen && len>=4*p){ int nonconst=0; for(long z=st;z<st+p;z++) if(tape[z]!=tape[st]) nonconst=1;
            if(side){ long c=y+p; if(getenv("FIRST")){ if(bestcut<0||c<bestcut){bestcut=c;per=p;} } else if(c>bestcut){bestcut=c; per=p;} } else { if(bestcut<0||st<bestcut){bestcut=st;per=p;} } }
          y++;
        }
      }
      cut=bestcut;
      if(getenv("DUMP")&&cut>=0){ long k=0; if(side){for(long y=cut;y<=hi&&k<(1<<22)-2;y++)sd[k++]=48+tape[y];} else {for(long y=cut-1;y>=lo&&k<(1<<22)-2;y--)sd[k++]=48+tape[y];} sd[k]=0; }
    }
    if(pos<2||pos>T-2){printf("OOB\n");break;}
  }
}
