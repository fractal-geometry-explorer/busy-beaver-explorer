// perturb: direct simulation of 1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA--- in which the head part is steered: at each
// reset record 0^inf 1 B> 1 0 (10)^X T (X >= 36) the countdown X is replaced by a chosen X' and the run goes on with
// the same tail T.  This asks whether the tail is safe on its own, for phase lengths other than the true 3/2 orbit.
// usage: perturb SEED LO HI MAXRESETS MAXSTEPS [START]      (START D: the twin, mirrored)
//   LO >= 0:  X' uniform in [LO, HI]           LO = -1: X' = X + HI (a fixed shift)
//   LO = -2:  X' = X + uniform in [-HI, HI]    LO = -3: X' = X + one of -HI, 0, HI
//   LO = -4:  X' = X + 1 or X - 1              LO = -5: X' = about X * HI / 150 (growth ratio HI/100 per phase)
// Prints OK / STEPS, or HALT with the cell (from the last left record), the reset count, the phase's X' and how many
// left records into the phase, after the tape at that last record in P-blocks (as recp.c).
// With the environment variable CTX set, it also prints at every left record "T resets records-into-phase |" and the
// blocks around the rightmost cell the previous sweep reached (its turning point, in brackets), D capped at 9.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc,char**argv){
  srand(atoi(argv[1])); long LO=atol(argv[2]),HI=atol(argv[3]),MR=atol(argv[4]); double maxs=atof(argv[5]);
  long N=1<<26;
  int W[6][2]={{1,0},{0,0},{0,1},{1,0},{0,1},{1,0}};
  int Mv[6][2]={{1,-1},{-1,1},{1,-1},{-1,-1},{1,1},{-1,0}};
  int Nx[6][2]={{1,5},{2,4},{0,3},{1,3},{0,2},{0,-1}};
  unsigned char*t=calloc(N,1); unsigned char*sv=calloc(N,1); long svh=0,svhi=0; long h=N/8,lo=h,hi=h; int s=argc>6?argv[6][0]-'A':0; unsigned long long st=0; long nres=0,rec=0,lastX=0,recAtReset=0; long mxp=0; int CTX=getenv("CTX")!=0; long FROMREC=getenv("FROMREC")?atol(getenv("FROMREC")):0;
  while((double)st<maxs){
    if(h<=1||h>=N-2){printf("OUT OF TAPE\n");return 1;}
    int c=t[h];
    if(s==5&&c==1){{printf("REC %d |",sv[svh]); long k=svh+1; while(k<=svhi){long n=0; while(k<=svhi&&sv[k]==1&&sv[k+1]==0){n++;k+=2;} if(n)printf(" %ld",n); if(k>svhi)break; if(!(sv[k]==1&&sv[k+1]==0)){printf(" %c",sv[k]?'i':'o');k++;}} printf("\n");} printf("HALT at cell %ld from record, step %llu after %ld resets; phase X=%ld, %ld records into it\n",h-svh-1,st,nres,lastX,rec-recAtReset);return 0;}
    if(s==1&&h<lo){
      if(CTX&&rec>FROMREC&&svhi>0){ long pos=mxp; long k=svh+1; long bs[4096][2]; int nb=0, ib=-1;
        while(k<=svhi&&nb<4096){long n=0; long st0=k; while(k<=svhi&&sv[k]==1&&sv[k+1]==0){n++;k+=2;} int x=sv[k]; k++; bs[nb][0]=n; bs[nb][1]=x; if(ib<0&&pos<k&&pos>=st0) ib=nb; nb++; if(ib>=0&&nb>ib+4)break;}
        if(ib>=0){ printf("T %ld %ld |",nres,rec-recAtReset); for(int j=ib-2;j<=ib+3;j++){ if(j<0||j>=nb){printf(" -");continue;} long D=bs[j][0]; printf(" %s%ld%c%s", j==ib?"[":"", D>9?9:D, bs[j][1]?'i':'o', j==ib?"]":""); } printf("\n"); } }
      lo=h; rec++; mxp=h; svh=h; svhi=hi; memcpy(sv+h-2,t+h-2,hi-h+4);
      if(t[h]==1&&t[h-1]==1&&t[h+1]==0){
        long k=h+2,X=0; while(t[k]==1&&t[k+1]==0){X++;k+=2;}
        if(X>=36){
          nres++;
          if(nres>MR){printf("OK %ld resets, %llu steps, width %ld\n",nres-1,st,hi-lo);return 0;}
          long Xn=LO==-5?(X*HI+(rand()%150))/150:LO==-3?X+HI*(rand()%3-1):LO==-4?X+(rand()%2?1:-1):LO==-2?X+(rand()%(2*HI+1)-HI):(LO<0?X+HI:LO+rand()%(HI-LO+1));
          long d=2*(Xn-X); // shift T by d
          if(hi+d>=N-2){printf("OUT OF TAPE\n");return 1;}
          memmove(t+k+d,t+k,hi-k+2);
          if(d<0) memset(t+hi+d+2,0,-d);
          for(long j=0;j<Xn;j++){t[h+2+2*j]=1;t[h+3+2*j]=0;}
          hi+=d; if(hi<h+2) hi=h+2; lastX=Xn; recAtReset=rec;
        }
      }
    }
    t[h]=W[s][c]; h+=Mv[s][c]; s=Nx[s][c]; st++;
    if(h>hi)hi=h; if(h>mxp)mxp=h;
  }
  printf("STEPS %llu resets %ld\n",st,nres); return 0;
}
