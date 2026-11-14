// 7085: every entry into D reading 0 (C read 0 with a 0 on its left): is everything left of it blank?
#include <stdio.h>
#include <stdlib.h>
#define N (1<<24)
static unsigned char t[N];
int main(int c,char**v){const char*m="1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB";double mx=atof(v[1]);
 int W[6][2],D[6][2],S[6][2];for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*p=m+s*7+b*3;if(p[0]=='-'){S[s][b]=-1;continue;}W[s][b]=p[0]-'0';D[s][b]=p[1]=='R'?1:-1;S[s][b]=p[2]-'A';}
 long p=N/2,lo=p,hi=p;int s=0;long step=0,d0=0,d0edge=0,c0=0,c0_11=0,min3=1<<30;
 for(;step<mx;){int b=t[p];if(S[s][b]<0){printf("HALT %ld\n",step);return 0;}
  if(s==3&&b==0){d0++; if(p<=lo) d0edge++; else printf("interior D0 at step %ld pos %ld lo %ld\n",step,p-N/2,lo-N/2);}
  if(s==2&&b==0){c0++; if(t[p-1]==1&&t[p-2]==1){c0_11++; /* L2: size of the block left */ long k=0;while(t[p-1-k]==1)k++; int most=1; for(long q=p-1-k;q>=lo;q--) if(t[q]){most=0;break;} if(!most&&k<min3)min3=k; if(k==2&&!most)printf("d=2 interior at %ld\n",step);} }
  t[p]=W[s][b];p+=D[s][b];s=S[s][b];step++;if(p<lo)lo=p;if(p>hi)hi=p;}
 printf("steps %ld: C0 %ld, bounces (L2) %ld, smallest non-leftmost bounced block %ld, D0 %ld of which at/over the left end %ld; lo %ld hi %ld\n",step,c0,c0_11,min3,d0,d0edge,lo-N/2,hi-N/2);}
