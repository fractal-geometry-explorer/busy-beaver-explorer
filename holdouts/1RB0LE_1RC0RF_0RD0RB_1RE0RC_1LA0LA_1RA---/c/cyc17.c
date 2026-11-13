// cyc17: 1RB0LE_1RC0RF_0RD0RB_1RE0RC_1LA0LA_1RA--- from blank tape, direct simulation with the fill-sweep jump
//   E-record "0^(z+4) 1 0 1 1 1 0 (10)^m 1 E>0"  ->  "0^z 1 0 1 1 1 0 (10)^(m+4) 1 E>0"  in 4m+40 steps.
// Prints each cycle start: E-record "P 1 1 1 0^K 1 E>0" with K>=8: steps, K, prefix P (run-length).
// usage: cyc17 MAXCELLS MAXCYCLES [nojump]   ("C" lines: cycle starts; "D" lines: progress every 2^28 direct steps)
// nojump: plain simulation (the C lines agree with the jumping run, step counts included, through cycle 12).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
static void p128(u128 x){char b[50];int i=49;b[i]=0;if(!x){printf("0");return;}while(x){b[--i]='0'+(int)(x%10);x/=10;}printf("%s",b+i);}
int main(int argc,char**argv){
  long N=atol(argv[1]); int maxc=atoi(argv[2]); int jump=!(argc>3);
  // states A..F = 0..5 ; table [state][sym] = write, move(+1 R,-1 L), next ; next=-1 halt
  int W[6][2]={{1,0},{1,0},{0,0},{1,0},{1,0},{1,0}};
  int Mv[6][2]={{1,-1},{1,1},{1,1},{1,1},{-1,-1},{1,0}};
  int Nx[6][2]={{1,4},{2,5},{3,1},{4,2},{0,0},{0,-1}};
  // A0 1RB A1 0LE ; B0 1RC B1 0RF ; C0 0RD C1 0RB ; D0 1RE D1 0RC ; E0 1LA E1 0LA ; F0 1RA F1 ---
  unsigned char *t=calloc(N,1); long off=N/8, h=off, lo=off, hi=off; int s=0; u128 steps=0; int cyc=0; long dsteps=0;
  while(1){
    if(h<=0||h>=N-1){printf("OUT OF TAPE\n");break;}
    int c=t[h];
    if(s==5&&c==1){printf("HALT at ");p128(steps);printf("\n");break;}
    if(s==4&&c==0&&h==hi&&t[h-1]==1){
      // E-record
      // cycle start? 1 1 1 0^K 1 E>
      long j=h-2,K=0; while(j>=lo&&t[j]==0){K++;j--;}
      if(K>=8&&j-2>=lo&&t[j]==1&&t[j-1]==1&&t[j-2]==1){
        cyc++; printf("C %d steps ",cyc);p128(steps);printf(" K %ld len %ld direct %ld P ",K,h-lo,dsteps);
        long a=lo; int first=1;
        while(a<=j-3){long b=a;while(b<=j-3&&t[b]==t[a])b++; printf("%s%d",first?"":" ",t[a]); if(b-a>1)printf("^%ld",b-a); first=0; a=b;}
        printf("\n"); fflush(stdout);
        if(cyc>=maxc)break;
      }
      if(jump){
        // (10)^m 1 E>  : scan back from h-2
        long q=h-2,m=0; while(q-1>=lo&&t[q]==0&&t[q-1]==1){m++;q-=2;}
        // greedy pairs also ate the "1 0" ending the word 1 0 1 1 1 0; q is now at the word's 4th cell
        if(m>=2&&q-3>=lo&&t[q]==1&&t[q-1]==1&&t[q-2]==0&&t[q-3]==1){
          m-=1; q+=2; // now t[q]=0 is the word's last cell, as below
          long z=0,r=q-6; while(r>=lo&&t[r]==0){z++;r--;}
          if(z>=12){
            long k=(z-8)/4; // leave z-4k >= 8
            long nz=z-4*k, nm=m+4*k;
            long start=q-5-z; // first zero
            long p=start+nz; // write 1 0 1 1 1 0 (10)^nm 1
            if(p+6+2*nm+1+2>=N){printf("OUT OF TAPE\n");break;}
            unsigned char w6[6]={1,0,1,1,1,0}; for(int i=0;i<6;i++)t[p+i]=w6[i]; p+=6;
            for(long i=0;i<nm;i++){t[p++]=1;t[p++]=0;}
            t[p++]=1; for(long i=p;i<=h+8*k+2&&i<N;i++)t[i]=0;
            h=p; hi=h;
            steps+=(u128)k*(4*m+40)+(u128)8*k*(k-1);
            continue;
          }
        }
      }
    }
    t[h]=W[s][c]; int mv=Mv[s][c]; s=Nx[s][c]; h+=mv; steps++; dsteps++;
    if((dsteps&((1L<<28)-1))==0){printf("D direct %ld steps ",dsteps);p128(steps);printf(" h-lo %ld hi-lo %ld s %d\n",h-lo,hi-lo,s);fflush(stdout);}
    if(h<lo)lo=h; if(h>hi)hi=h;
  }
  printf("END steps ");p128(steps);printf(" cycles %d\n",cyc);
}
