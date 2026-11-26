// The tape as words at each sweep: every first visit of the right end after a visit of the left end, the tape
// read as [ones] then words 0^a 1^b, x=(3,1) y=(3,4) z=(1,6), others as (a,b).
// usage: rounds MACHINE STEPS [EVERY [START_STATE]]   (start state 4 runs the sibling table 1RB0LB_1RC0LD_..., mirrored)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define T (1<<24)
static unsigned char tape[T];
int main(int argc,char**argv){
  char*m=argv[1]; long long N=atoll(argv[2]); int every=argc>3?atoi(argv[3]):1;
  int w[6][2],d[6][2],n[6][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*x=m+7*s+3*b; if(x[0]=='-'){n[s][b]=-1;continue;} w[s][b]=x[0]-'0'; d[s][b]=x[1]=='R'?1:-1; n[s][b]=x[2]-'A';}
  long p=T/2,lo=p,hi=p; int s=argc>4?atoi(argv[4]):0; int last=0; long round=0;
  static char buf[1<<22];
  for(long long i=0;i<N;i++){int b=tape[p]; if(n[s][b]<0){printf("HALT %lld\n",i);return 0;} tape[p]=w[s][b]; p+=d[s][b]; s=n[s][b];
    if(p>hi){hi=p; if(last!=1){ last=1; round++;
        if(round%every==0){
        // tokenize lo..hi as 0+1+
        int k=0; long q=lo; while(q<=hi && tape[q]==0) q++;
        // print leading ones? tape starts with 1s
        int c1=0; while(q<=hi&&tape[q]==1){c1++;q++;}
        k+=sprintf(buf+k,"[%d]",c1);
        while(q<=hi){int a=0; while(q<=hi&&tape[q]==0){a++;q++;} int b1=0; while(q<=hi&&tape[q]==1){b1++;q++;}
          if(b1==0) break;
          if(a==3&&b1==1) buf[k++]='x'; else if(a==3&&b1==4) buf[k++]='y'; else if(a==1&&b1==6) buf[k++]='z';
          else k+=sprintf(buf+k,"(%d,%d)",a,b1);}
        buf[k]=0; printf("%lld %ld %s\n",i,round,buf);}
      }}
    if(p<lo){lo=p; last=-1;}
    if(p<2||p>T-3){printf("OUT\n");return 0;}
  }
  return 0;
}
