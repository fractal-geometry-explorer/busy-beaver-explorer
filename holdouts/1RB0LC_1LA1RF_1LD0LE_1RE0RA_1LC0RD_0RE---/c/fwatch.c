// fwatch: direct simulation; every entry into state F (the halting state reads 1 to halt) with the 17 cells around it.
// usage: ./fwatch MACHINE MAXSTEPS
// count F entries by context window (cells p-6..p+8 around F position), print counts and first step
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int W[6][2],Mv[6][2],N[6][2];
typedef struct {char ctx[32]; long long n, first, last;} E; E es[100000]; int ne=0;
int main(int c,char**v){
  char*m=v[1]; long long max=atoll(v[2]);
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*p=m+s*7+r*3; if(p[2]=='-'){N[s][r]=-1;continue;} W[s][r]=p[0]-'0';Mv[s][r]=p[1]=='R'?1:-1;N[s][r]=p[2]-'A';}
  long long S=1LL<<28; unsigned char*t=calloc(S,1); long long h=S/2; int st=0; long long tot=0;
  for(long long k=1;k<=max;k++){
    int r=t[h]; int ns=N[st][r]; if(ns<0){printf("HALT %lld\n",k);return 0;}
    t[h]=W[st][r]; h+=Mv[st][r]; st=ns;
    if(st==5){ tot++; char b[32]; int q=0; for(long long i=h-8;i<=h+8;i++){ if(i==h)b[q++]='[';b[q++]='0'+t[i]; if(i==h)b[q++]=']';} b[q]=0;
      int f=-1; for(int i=0;i<ne;i++) if(!strcmp(es[i].ctx,b)){f=i;break;}
      if(f<0&&ne<100000){f=ne++; strcpy(es[f].ctx,b); es[f].n=0; es[f].first=k;}
      if(f>=0){es[f].n++; es[f].last=k;} }
  }
  printf("total F entries %lld, contexts %d\n",tot,ne);
  for(int i=0;i<ne;i++) printf("%s %lld first %lld last %lld\n",es[i].ctx,es[i].n,es[i].first,es[i].last);
  return 0;}
