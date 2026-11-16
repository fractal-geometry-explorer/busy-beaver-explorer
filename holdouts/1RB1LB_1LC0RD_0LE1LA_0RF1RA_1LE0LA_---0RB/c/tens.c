/* Census of "10" defects and of the merge trigger y 0 x^k 0: ./tens N every. Tokenizes the tape (111, 110,
   10, 0, final 1) at every every-th new left cell; prints each 10 at token distance 3..ntok-30 from the right
   end (TEN) and each y 0 x^k 0 with the y at distance 31..ntok-31 (Y0X0). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int W[6][2],D[6][2],S[6][2];
/* every `every`-th new-left event: tokenize tape (greedy 111,110,10,0, final 1) and report
   "10" tokens at token distance 3..ntok-30 from the right, with the word before and the gap words after. */
int main(int argc,char**argv){
  const char*T="1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB";
  for(int i=0;i<6;i++)for(int r=0;r<2;r++){const char*g=T+7*i+3*r; if(g[0]=='-'){S[i][r]=-1;continue;} W[i][r]=g[0]-'0';D[i][r]=g[1]=='R'?1:-1;S[i][r]=g[2]-'A';}
  long N=atol(argv[1]); int every=atoi(argv[2]);
  long SZ=1L<<26; unsigned char*t=calloc(SZ,1); long p=SZ/2; int s=0; long lo=p,hi=p; long ev=0;
  int *tk=malloc(sizeof(int)*SZ/2); long *tp=malloc(sizeof(long)*SZ/2);
  long nsnap=0,nbad=0,nwith=0,nyx=0;
  for(long k=0;k<N;k++){
    int r=t[p]; if(S[s][r]<0){printf("HALT %ld\n",k);return 0;} t[p]=W[s][r]; int d=D[s][r]; s=S[s][r]; p+=d; if(p>hi)hi=p;
    if(p<lo){lo=p; ev++; if(ev%every==0){
      long h=hi; while(h>lo && t[h]==0) h--;
      long x=p,n=0; int ok=1;
      while(x<h){ /* types: 0=111 1=110 2=10 3=0 */
        if(t[x]==1&&t[x+1]==1&&x+2<=h&&t[x+2]==1){tk[n]=0;tp[n++]=x;x+=3;}
        else if(t[x]==1&&t[x+1]==1&&x+2<=h&&t[x+2]==0){tk[n]=1;tp[n++]=x;x+=3;}
        else if(t[x]==1&&t[x+1]==0){tk[n]=2;tp[n++]=x;x+=2;}
        else if(t[x]==0){tk[n]=3;tp[n++]=x;x+=1;}
        else {ok=0;break;}
      }
      nsnap++;
      if(!ok||x!=h){printf("PARSEFAIL %ld\n",k);continue;}
      { long ny0=0; for(long i=31;i+2<n-30;i++){ if(tk[i]==1 && tk[i+1]==3){ long j=i+2; while(j<n && tk[j]==0) j++; if(j>i+2 && j<n && tk[j]==3){ ny0++; printf("Y0X0 step %ld dist %ld k %ld\n",k,n-i,j-i-2);} } } nyx+=ny0; }
      int any=0;
      for(long i=1;i<n;i++) if(tk[i]==2 && n-i>2 && n-i<n-30){
        any=1; long j=i+1; int ally=1; while(j<n&&tk[j]<2){ if(tk[j]!=1) ally=0; j++;}
        if(ally && tk[i-1]!=0) nbad++;
        printf("TEN step %ld ntok %ld dist %ld before %d gaplen %ld ally %d\n",k,n,n-i,tk[i-1],j-i-1,ally);
      }
      nwith+=any;
      if(nsnap%2000==0){printf("STAT step %ld ntok %ld snaps %ld with10 %ld bad %ld y0x0 %ld\n",k,n,nsnap,nwith,nbad,nyx);fflush(stdout);}
    }}
  }
  printf("END snaps %ld with10 %ld bad %ld y0x0 %ld\n",nsnap,nwith,nbad,nyx);
}
