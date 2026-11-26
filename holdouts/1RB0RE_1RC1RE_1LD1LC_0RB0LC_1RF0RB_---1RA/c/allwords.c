// Does any word (w0=0, L bits) followed by K block periods and a final 0 ever halt in the model?  T laps each.
#include <stdio.h>
#include <stdlib.h>
enum{X,P,Y,Q};
static const unsigned char D[4][2]={{P,X},{X,Y},{X,Q},{Y,Y}}; static const unsigned char INV[4]={1,1,0,0};
int main(int c,char**v){ int L=atoi(v[1]),K=atoi(v[2]),T=atoi(v[3]); static unsigned char w[1<<20]; long halts=0,tot=0,maxh=0; long hist[8]={0};
  for(unsigned long m=0;m<(1UL<<(L-1));m++){ int n=L; w[0]=0; for(int i=1;i<L;i++) w[i]=(m>>(i-1))&1;
    for(int k=0;k<K;k++){w[n++]=0;w[n++]=0;w[n++]=1;w[n++]=1;} w[n++]=0; tot++; long mg=1<<30;
    for(int t=1;t<=T;t++){ int s=X,last=0; for(int j=1;j<n;j++){int b=w[j]; w[j]=b^INV[s]; s=D[s][b]; if(s>=Y) last=j;}
      if(s==X||s==Q){ halts++; if(t>maxh)maxh=t; if(halts<=5) printf("HALT word %lx lap %d n=%d\n",m,t,n); break; }
      if(s==P){w[n++]=1;w[n++]=0;} else {w[n++]=1;w[n++]=1;w[n++]=0;} if(n-last<mg) mg=n-last; }
    hist[mg<=2?0:mg<=4?1:mg<=8?2:mg<=12?3:4]++; }
  printf("L=%d K=%d T=%d: %ld words, %ld halt (latest at lap %ld); min gap <=2:%ld <=4:%ld <=8:%ld <=12:%ld more:%ld\n",L,K,T,tot,halts,maxh,hist[0],hist[1],hist[2],hist[3],hist[4]); return 0; }
