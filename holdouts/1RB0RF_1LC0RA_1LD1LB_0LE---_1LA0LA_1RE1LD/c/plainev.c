// plain simulator: prints "step side state cells" when the head is about to read a never-visited cell on the side
// opposite to the last such event (the events of wrsim mode 0); cells of the visited region, '|' marks the head.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc,char**argv){const char*M=argv[1];long long maxs=atoll(argv[2]);long maxl=atol(argv[3]);
 int ns=(strlen(M)+1)/7;int W[8][2],Mv[8][2],Q[8][2],H[8][2];
 for(int q=0;q<ns;q++)for(int b=0;b<2;b++){const char*s=M+7*q+3*b;H[q][b]=(s[2]=='-');if(!H[q][b]){W[q][b]=s[0]-'0';Mv[q][b]=s[1]=='R'?1:-1;Q[q][b]=s[2]-'A';}}
 long N=1<<26;char*t=calloc(N,1);long pos=N/2,lo=pos,hi=pos-1;int q=0,last=0;long lines=0;
 for(long long st=0;st<maxs;st++){
  if(pos<lo||pos>hi){int side=pos<lo?-1:1; if(side!=last){printf("%lld %c %c ",st,side<0?'L':'R','A'+q);if(side<0)putchar('|');for(long i=lo;i<=hi;i++)putchar('0'+t[i]);if(side>0)putchar('|');putchar('\n');last=side;if(++lines>=maxl)break;}
   if(pos<lo)lo=pos;if(pos>hi)hi=pos;}
  int b=t[pos];if(H[q][b]){printf("HALT %lld\n",st+1);break;}t[pos]=W[q][b];pos+=Mv[q][b];q=Q[q][b];if(pos<1||pos>=N-1){fprintf(stderr,"tape\n");break;}}
}
