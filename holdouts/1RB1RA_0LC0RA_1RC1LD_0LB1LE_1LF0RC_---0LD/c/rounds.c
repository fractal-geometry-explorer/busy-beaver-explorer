// Run 1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD from blank tape and print each round start "W k N step":
// the tape is then 0^inf W (100)^k 1 0 (110)^N 1 1 1 B> 0^inf.  gcc -O2 -o rounds rounds.c && ./rounds
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define SZ (1<<24)
static unsigned char t[SZ];
int main(){
  // A0 1RB A1 1RA B0 0LC B1 0RA C0 1RC C1 1LD D0 0LB D1 1LE E0 1LF E1 0RC F0 --- F1 0LD
  int W[6][2]={{1,1},{0,0},{1,1},{0,1},{1,0},{-1,0}}, Mv[6][2]={{1,1},{-1,1},{1,-1},{-1,-1},{-1,1},{0,-1}}, S[6][2]={{1,0},{2,0},{2,3},{1,4},{5,2},{-1,3}};
  {
    memset(t,0,SZ); long long p=SZ/2; long long lo=p;
    
    long long hi=p, h=p; int st=0; long long n=0; int done=0;
    while(n<60000000000LL){
      int s=t[h]; int ns=S[st][s];
      if(ns<0){printf("HALT %lld\n",n);done=1;break;}
      t[h]=W[st][s]; h+=Mv[st][s]; st=ns; n++;
      if(h<lo) lo=h; if(h<2||h>SZ-2){printf("OVF\n");done=1;break;}
      if(h>hi){hi=h;
        if(st==1 && t[h-1]==1&&t[h-2]==1&&t[h-3]==1){
          long long q=h-3, NN=0; while(t[q-1]==0&&t[q-2]==1&&t[q-3]==1){q-=3;NN++;}
          if(t[q-1]==0&&t[q-2]==1){ q-=2; long long kk=0; while(t[q-1]==0&&t[q-2]==0&&t[q-3]==1){q-=3;kk++;}
            long long a=lo; while(t[a]==0&&a<q)a++;
            char buf[300];int L=0; for(long long x=a;x<q&&L<290;x++)buf[L++]='0'+t[x]; buf[L]=0;
            printf("%s %lld %lld %lld\n",L?buf:"-",kk,NN,n);fflush(stdout);}
        }
      }
    }
    if(!done)printf("TIMEOUT\n");
    fflush(stdout);
  }
}
