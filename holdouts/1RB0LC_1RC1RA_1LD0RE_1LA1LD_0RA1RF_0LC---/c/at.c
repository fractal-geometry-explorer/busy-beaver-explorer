// at MACHINE STEPS : state, head offset from leftmost nonzero-or-head cell, tape string
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<28)
static unsigned char tape[N];
int main(int c,char**v){
  int W[6][2],D[6][2],S[6][2];
  for(int i=0;i<6;i++)for(int b=0;b<2;b++){const char*t=v[1]+7*i+3*b; if(t[0]=='-'){S[i][b]=-1;W[i][b]=0;D[i][b]=1;}else{W[i][b]=t[0]-'0';D[i][b]=t[1]=='R'?1:-1;S[i][b]=t[2]-'A';}}
  long long max=atoll(v[2]);long pos=N/2,lo=pos,hi=pos;int st=0;long long k;
  for(k=0;k<max;k++){int b=tape[pos];int ns=S[st][b];if(ns<0){printf("HALT %lld\n",k+1);return 0;}
    tape[pos]=W[st][b];pos+=D[st][b];st=ns;if(pos<lo)lo=pos;if(pos>hi)hi=pos;}
  long a=lo,b=hi;while(a<b&&!tape[a])a++;while(b>a&&!tape[b])b--;
  printf("%c %ld ",'A'+st,pos-a);for(long i=a;i<=b;i++)putchar('0'+tape[i]);putchar('\n');return 0;}
