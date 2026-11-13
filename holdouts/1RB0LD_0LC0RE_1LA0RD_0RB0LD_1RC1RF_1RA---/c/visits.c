// ev5 M maxsteps: (a) at each left extension: the A@65 event before and 2 after ("LV"); (b) each E1 with tape ("E1")
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<22)
unsigned char tape[N];
char buf[2][200000];
int main(int argc,char**argv){
  char*m=argv[1]; long long mx=atoll(argv[2]); long P=65; int S=0; int K=2;
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*p=m+s*7+r*3; if(p[2]=='-'){ns[s][r]=-1;continue;} nw[s][r]=p[0]-'0'; mv[s][r]=p[1]=='R'?1:-1; ns[s][r]=p[2]-'A';}
  long pos=N/2,lo=pos,hi=pos; int st=0; long long t=0,cnt=0; int after=-1;
  while(t<mx){int r=tape[pos]; int s2=ns[st][r]; if(s2<0){printf("HALT %lld\n",t+1);fflush(stdout);return 0;}
    if(pos-N/2==P && st==S){ cnt++; char*b=buf[0]; int k=sprintf(b,"EV %lld %lld %ld ",cnt,t,lo-N/2); for(long i=lo;i<=hi;i++){ if(i==pos)b[k++]='|';b[k++]='0'+tape[i];} b[k]=0;
      if(after>0){puts(b); after--; if(!after)fflush(stdout);} else strcpy(buf[1],b); }
    if(st==4 && r==1){printf("E1 %lld %lld %ld %ld ",cnt,t,pos-N/2,lo-N/2); for(long i=lo;i<=hi;i++){ if(i==pos)putchar('[');putchar('0'+tape[i]); if(i==pos)putchar(']');} putchar('\n');fflush(stdout);}
    tape[pos]=nw[st][r]; pos+=mv[st][r]; st=s2; t++;
    if(pos>hi)hi=pos;
    if(pos<lo){lo=pos; puts(buf[1]); after=K; }
  }
  printf("END %lld\n",t);
}
