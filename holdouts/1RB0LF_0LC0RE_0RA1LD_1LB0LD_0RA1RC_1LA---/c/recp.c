// recp: 1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA--- from blank tape; at each left record (state B left of the
// previous record) print "steps recno width headcell |" and the tape right of the head as P-blocks: k = (10)^k,
// i / o = a single 1 / 0 cell.  usage: recp MAXCELLS MAXSTEPS EVERY MAXTOK
#include <stdio.h>
#include <stdlib.h>
int main(int argc,char**argv){
  long N=atol(argv[1]); double maxs=atof(argv[2]); long every=atol(argv[3]); int maxtok=atoi(argv[4]);
  int W[6][2]={{1,0},{0,0},{0,1},{1,0},{0,1},{1,0}};
  int Mv[6][2]={{1,-1},{-1,1},{1,-1},{-1,-1},{1,1},{-1,0}};
  int Nx[6][2]={{1,5},{2,4},{0,3},{1,3},{0,2},{0,-1}};
  unsigned char*t=calloc(N,1); long h=N-N/8,lo=h,hi=h; int s=0; unsigned long long st=0; long rec=0;
  while((double)st<maxs){
    if(h<=1||h>=N-1){printf("OUT OF TAPE\n");break;}
    int c=t[h];
    if(s==5&&c==1){printf("HALT at %llu\n",st);return 0;}
    if(s==1&&h<lo){
      lo=h; rec++;
      if(rec%every==0){
        printf("%llu %ld %ld %d |",st,rec,hi-lo+1,t[h]);
        long k=h+1; int cnt=0;
        while(k<=hi&&cnt<maxtok){
          long n=0; while(k+1<=hi+1&&t[k]==1&&t[k+1]==0){n++;k+=2;}
          if(n) {printf(" %ld",n);cnt++;}
          if(k>hi)break;
          if(!(t[k]==1&&t[k+1]==0)){printf(" %c",t[k]?'i':'o');k++;cnt++;}
        }
        printf("\n"); fflush(stdout);
      }
    }
    t[h]=W[s][c]; h+=Mv[s][c]; s=Nx[s][c]; st++; if(h>hi)hi=h;
  }
  printf("END %llu rec %ld width %ld\n",st,rec,hi-lo+1);
}
