/* fresh MACHINE NPAIRS DVISITS OUTCELLS [SKIP] : the family 1RB1RC_1LC0RE_1LD0LB_1RA1LC_*: start at a visit with
 * block 1^16 and R = (01)^NPAIRS 1 1 (fresh reservoir); run double-visits with the block reset to 16 cells each
 * visit; after each double-visit (from number SKIP on) print: depth(max head position in R during it, cells) and the
 * first OUTCELLS cells of R. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int W[6][2],D[6][2],S[6][2];
int main(int c,char**v){ const char*m=v[1];
 for(int i=0;i<6;i++)for(int b=0;b<2;b++){const char*t=m+7*i+3*b; if(t[0]=='-')S[i][b]=-1; else {W[i][b]=t[0]-'0';D[i][b]=t[1]=='R'?1:-1;S[i][b]=t[2]-'A';}}
 long NP=atol(v[2]), DV=atol(v[3]); int OC=atoi(v[4]); long SKIP=c>5?atol(v[5]):0; int w=16;
 long len=w+2*NP+2+64; unsigned char*tp=calloc(len,1); for(int i=0;i<w;i++)tp[i]=1; for(long i=0;i<NP;i++){tp[w+2*i]=0;tp[w+2*i+1]=1;} tp[w+2*NP]=1; tp[w+2*NP+1]=1;
 for(long dv=1;dv<=DV;dv++){ long mh=0;
   for(int t=0;t<2;t++){ long h=0; int s=0;
     for(;;){ if(h<0){ if(s!=3){printf("EXIT %c at dv %ld\n",65+s,dv);return 0;} break;} int y=tp[h]; int ns=S[s][y]; if(ns<0){printf("HALT at dv %ld h=%ld\n",dv,h-w);return 0;} tp[h]=W[s][y]; h+=D[s][y]; s=ns; if(h>mh)mh=h; if(h>=len-2){printf("END at dv %ld\n",dv);return 0;} } }
   if(dv>=SKIP){ printf("%ld ",mh-w); fwrite("",0,0,stdout); for(int i=0;i<OC;i++)putchar('0'+tp[w+i]); putchar('\n'); } }
 return 0; }
