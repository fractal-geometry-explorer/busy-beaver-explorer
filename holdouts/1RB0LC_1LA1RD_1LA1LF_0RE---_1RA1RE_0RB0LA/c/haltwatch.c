// haltwatch MACHINE STEPS : how often each transition is used in the first STEPS steps from blank tape, and the 7-cell window around the head each time the halting state is entered.  gcc -O2 -o haltwatch haltwatch.c
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int W[6][2],Mv[6][2],N[6][2];
int main(int c,char**v){char*m=v[1];int hs=-1,hb=-1;for(int i=0;i<6;i++)for(int b=0;b<2;b++){char*p=m+i*7+b*3;if(p[2]=='-'){N[i][b]=-1;hs=i;hb=b;}else{W[i][b]=p[0]-'0';Mv[i][b]=p[1]=='R'?1:-1;N[i][b]=p[2]-'A';}}
 long long max=atoll(v[2]); int SZ=1<<25; unsigned char*t=calloc(SZ,1); long h=SZ/2; int s=0; long long cnt[6][2]={0}; long long win[256]={0};
 for(long long k=0;k<max;k++){int b=t[h]; if(N[s][b]<0){printf("HALT %lld\n",k+1);break;} cnt[s][b]++; t[h]=W[s][b]; h+=Mv[s][b]; s=N[s][b];
   if(s==hs){int w=0; for(int d=-3;d<=3;d++) if(d) w=w*2+t[h+d]; else w=w*2+t[h]; win[w&127]++;}}
 for(int i=0;i<6;i++)printf("%c: %lld %lld\n",'A'+i,cnt[i][0],cnt[i][1]);
 printf("windows (7 cells, head in middle) when entering halting state %c (halts on %d):\n",'A'+hs,hb);
 for(int w=0;w<128;w++) if(win[w]){for(int j=6;j>=0;j--){if(j==3)putchar('[');putchar('0'+((w>>j)&1));if(j==3)putchar(']');} printf(" %lld\n",win[w]);}
}
