/* gaps.c: each time the head moves right from a 1 onto a 0, count (state, length of the run of 0s ahead, whether it reaches the end of the tape). usage: gaps MACHINE STEPS.  Shared by the G11 batch-4 folders. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
// record (state, gap length mod 8, cap) whenever a right-moving step lands the head on a 0 with a 1 to its left
int main(int c,char**v){char*M=v[1];long long T=atoll(v[2]);
 int w[6][2],mv[6][2],nx[6][2];
 for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*p=M+7*s+3*r; if(p[2]=='-'){nx[s][r]=-1;continue;} w[s][r]=p[0]-'0';mv[s][r]=p[1]=='R'?1:-1;nx[s][r]=p[2]-'A';}
 int N=1<<22; unsigned char*t=calloc(N,1); long h=N/2,lo=h,hi=h; int st=0;
 static long long cnt[6][64][2];
 for(long long k=1;k<=T;k++){int r=t[h]; int s2=nx[st][r]; if(s2<0){printf("halt %lld\n",k);return 0;}
  t[h]=w[st][r]; int m=mv[st][r]; h+=m; st=s2; if(h>hi)hi=h; if(h<lo)lo=h;
  if(m==1 && t[h]==0 && t[h-1]==1){ int L=0; while(h+L<=hi && t[h+L]==0 && L<63) L++; int blank= (h+L>hi); cnt[st][L][blank]++; }
 }
 for(int s=0;s<6;s++)for(int L=0;L<64;L++)for(int b=0;b<2;b++) if(cnt[s][L][b]) printf("%c gap %d%s: %lld\n",'A'+s,L,b?"(end)":"",cnt[s][L][b]);
}
