// ev: run a machine from blank tape and print the tape, compressed as (word)^n, each time the head reaches a new cell.
// usage: ev MACHINE MAXSTEPS SIDE(L|R|B) STATE(A-F|*) EVERY MAXLINES [MAXWORD]   (head shown as [S] before its cell)
// ev MACHINE MAXSTEPS SIDE(L|R|B) STATE(A-F|*) EVERYNTH MAXLINES [MAXW]
// prints tape compressed (word^n) each time head reaches new cell on SIDE in STATE; head marked by [S]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int nw[6][2],mv[6][2],ns[6][2];
#define N (1<<24)
unsigned char tape[N];
int maxw=8;
void comp(int lo,int hi,int head,int st){
  int i=lo;
  while(i<=hi){
    if(i==head){printf("[%c]",'A'+st);}
    int bk=0,bw=1;
    for(int w=1;w<=maxw;w++){ if(i+w>hi+1)break; int k=1;
      while(i+(k+1)*w<=hi+1 && memcmp(tape+i,tape+i+k*w,w)==0 && !(head>i+k*w-1 && head<i+(k+1)*w && head!=i+k*w) ) {k++;}
      // don't let a repeat span head
      if(head>i && head<=i+k*w-1){ int kk=(head-i)/w; if(kk<k) k=kk;}
      if(k>=3 && k*w>bk*bw){bk=k;bw=w;}
    }
    if(bk>=3){putchar('(');for(int j=0;j<bw;j++)putchar('0'+tape[i+j]);printf(")^%d ",bk);i+=bk*bw;}
    else {putchar('0'+tape[i]);putchar(' ');i++;}
  }
  putchar('\n');
}
int main(int c,char**v){
  char*m=v[1];long long max=atoll(v[2]);char side=v[3][0];char sst=v[4][0];long long every=atoll(v[5]);long long ml=atoll(v[6]); if(c>7)maxw=atoi(v[7]);
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*t=m+7*s+3*r; if(t[2]=='-'){ns[s][r]=-1;continue;} nw[s][r]=t[0]-'0';mv[s][r]=t[1]=='R'?1:-1;ns[s][r]=t[2]-'A';}
  int p=N/2,lo=p,hi=p,st=0;long long cnt=0,lines=0;
  for(long long k=1;k<=max;k++){
    int r=tape[p]; int t=ns[st][r]; if(t<0){printf("HALT %lld\n",k);return 0;}
    tape[p]=nw[st][r];p+=mv[st][r];st=t;
    if(p<lo||p>hi){ char sd=p<lo?'L':'R'; if(p<lo)lo=p; else hi=p;
      if((side=='B'||side==sd)&&(sst=='*'||sst-'A'==st)){ cnt++; if(cnt%every==0){printf("%lld %c w=%d o=%d: ",k,sd,hi-lo+1,N/2-lo);comp(lo,hi,p,st);if(++lines>=ml)return 0;}}
      if(lo<10||hi>N-10){printf("OUT\n");return 0;}
    }
  }
  return 0;
}
