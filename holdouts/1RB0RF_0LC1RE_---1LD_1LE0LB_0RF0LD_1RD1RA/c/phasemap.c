// Phase map of 1RB0RF_0LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA.
// C(e) = 0^inf 1 E> 0 (01)^e 0^inf.
// usage: phasemap E0 E1 MAXSTEPS        -> for each e in E0..E1: "e e2 steps" (C(e) -> C(e2); e2 = -2: halts, -1: not within MAXSTEPS)
//        phasemap 0 0 MAXSTEPS blank    -> run from blank tape, print "step e" at every C(e)
// build: gcc -O2 -o phasemap phasemap.c
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int nx[6][2]={{1,5},{2,4},{-1,3},{4,1},{5,3},{3,0}}, wr[6][2]={{1,0},{0,1},{0,1},{1,0},{0,0},{1,1}}, mv[6][2]={{1,1},{-1,1},{0,-1},{-1,-1},{1,-1},{1,1}};
#define SZ (1<<24)
unsigned char *t;
int main(int argc,char**argv){
  int blank=argc>4; long e0=atol(argv[1]), e1=atol(argv[2]); long long maxs=atoll(argv[3]);
  t=malloc(SZ);
  for(long e=e0;e<=e1;e++){
    memset(t,0,SZ); long p=SZ/2; if(!blank){t[p-1]=1;} for(long i=0;i<(blank?0:e);i++){t[p+1+2*i]=0;t[p+2+2*i]=1;}
    long lo=p-1,hi=p+2*e; int s=blank?0:4; long long n=0; long res=-1;
    while(n<maxs){int b=t[p]; if(nx[s][b]<0){res=-2;break;} t[p]=wr[s][b]; p+=mv[s][b]; s=nx[s][b]; n++;
      if(p<lo)lo=p; if(p>hi)hi=p;
      if(s==4 && t[p]==0 && t[p-1]==1 && !t[p-2] && !t[p-3] && !t[p-4] && !t[p-5] && !t[p-6]){ // check clean: left of p-1 all zero, right is (01)^k then zeros
        int ok=1; for(long x=lo;x<p-1;x++) if(t[x]){ok=0;break;}
        if(!ok) continue;
        long x=p+1,k=0; while(x+1<=hi+1 && t[x]==0 && t[x+1]==1){x+=2;k++;}
        for(long y=x;y<=hi;y++) if(t[y]){ok=0;break;}
        if(ok){res=k;if(blank){printf("%lld %ld\n",n,k);fflush(stdout);continue;}break;}
      }
    }
    printf("%ld %ld %lld\n",e,res,n);
  }
}
