// 129887: at every left-end visit (a new cell on the left reached in state B) the tape must be a word over 110, 111
// (cut into 3-cell tokens from the cell right of the head). Also counts C1,D0,B1 events (one cell from the halt).
#include <stdio.h>
#include <stdlib.h>
#define N (1<<25)
static unsigned char t[N];
int main(int c,char**v){const char*m="1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA";double mx=atof(v[1]);
 int W[6][2],D[6][2],S[6][2];for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*p=m+s*7+b*3;if(p[0]=='-'){S[s][b]=-1;continue;}W[s][b]=p[0]-'0';D[s][b]=p[1]=='R'?1:-1;S[s][b]=p[2]-'A';}
 long p=N/2,lo=p,hi=p;int s=0,prev=-1,prev2=-1;long step=0,vis=0,bad=0,near=0,nearbad=0,maxlen=0;
 for(;step<mx;){int b=t[p];if(S[s][b]<0){printf("HALT %ld\n",step);return 0;}
  if(p<lo&&s==1){vis++;long n=hi-p; /* cells p+1..hi */ long e=hi; while(e>p&&t[e]==0)e--; long len=e-p; if(len%3==2)len++; /* a final 110 */
    int ok=(len%3==0); for(long i=p+1;ok&&i<p+1+len;i+=3) if(!(t[i]==1&&t[i+1]==1)) ok=0; if(!ok){bad++; if(bad<=5)printf("visit %ld at step %ld is not a word\n",vis,step);} if(len/3>maxlen)maxlen=len/3;}
  if(s==1&&prev==3&&prev2==2&&b==1){near++; if(t[p-1]==0)nearbad++;}
  prev2=prev;prev=s;
  t[p]=W[s][b];p+=D[s][b];s=S[s][b];step++;if(p<lo-1)lo=p+1;if(p>hi)hi=p;}
 printf("steps %ld: left-end visits %ld, not words over 110/111: %ld, longest word %ld tokens; C1 D0 B1 events %ld, with a 0 on the left (halt) %ld\n",step,vis,bad,maxlen,near,nearbad);}
