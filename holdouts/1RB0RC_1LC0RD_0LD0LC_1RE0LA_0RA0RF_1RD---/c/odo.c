// odo MACHINE STEPS MODE: sample the run each time the head arrives at the left end of the tape in state D with 1000
// there; print "step width | k gadget k gadget ..." (k = number of 1000s, gadget = the cells up to the next 1000)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<25)
unsigned char tape[N];
char buf[1<<22], shape[1<<20], pshape[1<<20], prevline[1<<22];
int main(int argc,char**argv){
  char*m=argv[1]; long long steps=atoll(argv[2]); int mode=atoi(argv[3]); char want=argc>4?argv[4][0]:'D';
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*t=m+s*7+r*3; if(t[0]=='-'){ns[s][r]=-1;continue;} nw[s][r]=t[0]-'0'; mv[s][r]=t[1]=='R'?1:-1; ns[s][r]=t[2]-'A';}
  long pos=N/2,lo=pos,hi=pos; int st=0; long prevpos=pos; pshape[0]=0; prevline[0]=0; long long skipped=0;
  for(long long i=0;i<steps;i++){
    int r=tape[pos]; int n=ns[st][r]; if(n<0){printf("HALT %lld\n",i+1);return 0;}
    tape[pos]=nw[st][r]; pos+=mv[st][r]; st=n;
    if(pos<lo)lo=pos; if(pos>hi)hi=pos;
    if(pos==lo && prevpos!=lo && st==want-'A' && tape[lo]==1 && tape[lo+1]==0 && tape[lo+2]==0 && tape[lo+3]==0){
      // parse
      char*o=buf; char*sh=shape; o+=sprintf(o,"%lld %ld |",i+1,hi-lo+1);
      long p=lo; 
      while(p<=hi){
        long k=0; while(p+3<=hi && tape[p]==1&&tape[p+1]==0&&tape[p+2]==0&&tape[p+3]==0){k++;p+=4;}
        o+=sprintf(o," %ld",k);
        if(p>hi)break;
        // gadget
        char g[256]; int gl=0;
        while(p<=hi && !(p+3<=hi && tape[p]==1&&tape[p+1]==0&&tape[p+2]==0&&tape[p+3]==0)){ if(gl<250)g[gl++]='0'+tape[p]; p++;}
        g[gl]=0;
        const char*nm=g;
        o+=sprintf(o," %s",nm); sh+=sprintf(sh," %s",nm);
      }
      if(mode==0) puts(buf);
      else { if(strcmp(shape,pshape)){ if(skipped>0) printf("  [%lld] %s\n",skipped,prevline); puts(buf); skipped=0; strcpy(pshape,shape);} else {skipped++; strcpy(prevline,buf);} }
      fflush(stdout);
    }
    prevpos=pos;
  }
  return 0;}
