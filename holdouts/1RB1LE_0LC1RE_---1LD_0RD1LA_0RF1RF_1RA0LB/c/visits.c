// direct cell-level run; prints "visit step" at the visits (the head in state S on a new cell at the right end)
// usage: visits MACHINE maxsteps S from_visit to_visit every
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int W[6][2],Mv[6][2],Nx[6][2];
int main(int c,char**v){ const char*m=v[1];
 for(int s=0;s<6;s++)for(int r=0;r<2;r++){ const char*q=m+s*7+r*3; if(q[0]=='-'){Nx[s][r]=-1;} else {W[s][r]=q[0]-'0';Mv[s][r]=q[1]=='R'?1:-1;Nx[s][r]=q[2]-'A';} }
 double mx=atof(v[2]); int vs=v[3][0]-'A'; long from=atol(v[4]),to=atol(v[5]),every=atol(v[6]);
 long SZ=1L<<26; char*t=calloc(SZ,1); long p=SZ/2,lo=p,hi=p; int s=0; unsigned long long n=0; long nv=0;
 for(;;){ if((double)n>=mx)break;
  if(p>hi){ hi=p; if(s==vs){ nv++; if(nv>=from&&nv<=to&&(nv-from)%every==0){ printf("%ld %llu ",nv,n);
      putchar(10); } if(nv>to)break; } }
  if(p<lo)lo=p;
  int r=t[p]; if(Nx[s][r]<0){printf("HALT %llu\n",n+1);break;} t[p]=W[s][r]; int ns=Nx[s][r]; p+=Mv[s][r]; s=ns; n++; }
 return 0;}
