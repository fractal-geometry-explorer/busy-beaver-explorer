// busyl M STATEFILE N: load a tape (t pos state lo hi tape, as written by tmx -save), run N steps, report end visits and
// the visit count of every (cell, state) and the final tape. gcc -O2 -o busyl busyl.c
#include <stdio.h>
#include <stdlib.h>
#define N (1<<22)
unsigned char tape[N]; long long cnt[N][6];
int main(int argc,char**argv){char*m=argv[1]; long long mx=atoll(argv[3]); int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*p=m+s*7+r*3; if(p[2]=='-'){ns[s][r]=-1;continue;} nw[s][r]=p[0]-'0'; mv[s][r]=p[1]=='R'?1:-1; ns[s][r]=p[2]-'A';}
  FILE*f=fopen(argv[2],"r"); long long t; long p,l,h; int st; fscanf(f,"%lld %ld %d %ld %ld ",&t,&p,&st,&l,&h);
  long pos=p+N/2,lo=l+N/2,hi=h+N/2; for(long i=lo;i<=hi;i++){int c=fgetc(f); tape[i]=c-'0';} fclose(f);
  for(long long k=0;k<mx;k++){int r=tape[pos]; int s2=ns[st][r]; if(s2<0){printf("HALT %lld\n",t+k+1);return 0;} cnt[pos][st]++;
   tape[pos]=nw[st][r]; pos+=mv[st][r]; st=s2; if(pos<lo){lo=pos;printf("left end %ld at %lld\n",lo-N/2,t+k);} if(pos>hi){hi=pos;printf("right end %ld at %lld\n",hi-N/2,t+k);}}
  printf("lo %ld hi %ld pos %ld\n",lo-N/2,hi-N/2,pos-N/2);
  for(long i=lo;i<=hi;i++){printf("%ld",i-N/2); for(int s=0;s<6;s++)printf(" %lld",cnt[i][s]); printf(" %d\n",tape[i]);}
}
