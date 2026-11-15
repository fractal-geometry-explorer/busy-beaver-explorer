// direct run of 1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA: "visit step hash tokens" at every visit, a visit being
// the head in B on a blank cell with blank tape on its left (to compare with "wrun dump").  usage: dvis STEPS
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#define N (1<<25)
static unsigned char t[N];
int main(int c,char**v){const char*m="1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA";double mx=atof(v[1]);
 int W[6][2],D[6][2],S[6][2];for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*p=m+s*7+b*3;if(p[0]=='-'){S[s][b]=-1;continue;}W[s][b]=p[0]-'0';D[s][b]=p[1]=='R'?1:-1;S[s][b]=p[2]-'A';}
 long p=N/2,hi=p,left=N;   /* left: the leftmost 1 (N if none) */
 int s=0;long step=0,vis=0;
 for(;step<mx;){int b=t[p];if(S[s][b]<0){printf("HALT %ld\n",step+1);return 0;}
  if(s==1&&b==0&&p<left&&left<N){vis++;long e=hi; while(e>p&&t[e]==0)e--; long len=e-p; while(len%3)len++;
    uint64_t h=1469598103934665603ULL; int ok=1; for(long i=p+1;i<p+1+len;i+=3){ if(!(t[i]==1&&t[i+1]==1)) ok=0; h^=(unsigned char)(t[i+2]?'c':'b'); h*=1099511628211ULL; }
    printf("%ld %ld %016lx %ld%s\n",vis,step,(unsigned long)h,len/3,ok?"":" NOTWORD"); }
  int w=W[s][b]; t[p]=w;
  if(w){ if(p<left) left=p; } else if(p==left){ while(left<=hi&&t[left]==0) left++; if(left>hi) left=N; }
  p+=D[s][b];s=S[s][b];step++;if(p>hi)hi=p; if(p<8||p>N-8){fprintf(stderr,"tape\n");return 1;}}
 return 0;}
