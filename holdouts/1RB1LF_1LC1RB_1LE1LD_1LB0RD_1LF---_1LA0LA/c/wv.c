// wall visits: head in F on a 0, at a new leftmost position. prints visit#, step, tape right of the wall.
// usage: wv MACHINE maxsteps fromstep every [untilstep]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned long long u64;
int W[6][2],Mv[6][2],Nx[6][2];
int main(int c,char**v){ const char*m=v[1];
 for(int s=0;s<6;s++)for(int r=0;r<2;r++){ const char*q=m+s*7+r*3; if(q[0]=='-'){Nx[s][r]=-1;} else {W[s][r]=q[0]-'0';Mv[s][r]=q[1]=='R'?1:-1;Nx[s][r]=q[2]-'A';} }
 double mx=atof(v[2]); double from=atof(v[3]); long every=atol(v[4]);
 long SZ=1L<<27; char*t=calloc(SZ,1); long p=SZ-4096,lo=p,hi=p,z=p; int s=0; u64 n=0; long vis=0;
 while((double)n<mx){ int r=t[p]; if(Nx[s][r]<0){printf("HALT %llu\n",n+1);break;}
   t[p]=W[s][r]; p+=Mv[s][r]; s=Nx[s][r]; n++;
   if(p>hi){hi=p; printf("RIGHT %llu %c %ld\n",n,'A'+s,hi-z);}
   if(p<lo){ lo=p; if(s==5&&t[p]==0){ vis++; if((double)n>=from && vis%every==0){ printf("%ld %llu %ld ",vis,n,lo-z); for(long i=p+1;i<=hi;i++)putchar('0'+t[i]); putchar('\n'); } } }
 }
 return 0; }
