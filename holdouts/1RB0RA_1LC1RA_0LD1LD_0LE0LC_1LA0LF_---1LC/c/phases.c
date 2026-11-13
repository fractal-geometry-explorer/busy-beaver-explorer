#include <stdio.h>
#include <stdlib.h>
/* 1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC: print main phase starts A>0 10 00 (10)^y with y>=100 */
#define N (1L<<24)
static unsigned char t[N];
int main(int c,char**v){ long max=atol(v[1]);
 int W[6][2]={{1,0},{1,1},{0,1},{0,0},{1,0},{-1,1}}; int D[6][2]={{1,1},{-1,1},{-1,-1},{-1,-1},{-1,-1},{0,-1}};
 int S[6][2]={{1,0},{2,0},{3,3},{4,2},{0,5},{-1,2}};
 long p=N/2,mn=p,mx=p; int s=0; long n;
 for(n=0;n<max;n++){ int b=t[p];
  if(s==0&&p<=mn&&t[p+1]==1&&t[p+2]==0&&t[p+3]==0&&t[p+4]==0){ long y=0,q=p+5; while(t[q]==1&&t[q+1]==0){y++;q+=2;} if(y>=100){printf("%ld %ld\n",n,y);fflush(stdout);} }
  if(S[s][b]<0){printf("HALT %ld\n",n);return 0;}
  t[p]=W[s][b]; p+=D[s][b]; s=S[s][b]; if(p<mn)mn=p; if(p>mx)mx=p;
  if(p<2||p>N-3){printf("OUT %ld\n",n);return 0;} }
 printf("END %ld %ld\n",n,mx-mn); return 0;}
