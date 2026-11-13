// events.c (scratch tool, copied for reproducibility).  usage: gcc -O2 -o events c/events.c; ./events MACHINE MAXSTEPS SIDE(L|R|B) EVERY name=word ...  : on each new-cell event on SIDE, every EVERY-th, print word-RLE tape
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<24)
unsigned char tape[N]; int T[6][2][3];
char *wn[16], *wd[16]; int wl[16], nw=0;
int main(int argc,char**argv){
  char*m=argv[1]; long long max=atoll(argv[2]); char side=argv[3][0]; long long every=atoll(argv[4]);
  for(int i=5;i<argc;i++){ char*e=strchr(argv[i],'='); *e=0; wn[nw]=argv[i]; wd[nw]=e+1; wl[nw]=strlen(e+1); nw++; }
  // sort by length desc
  for(int i=0;i<nw;i++)for(int j=i+1;j<nw;j++) if(wl[j]>wl[i]){char*t=wn[i];wn[i]=wn[j];wn[j]=t;t=wd[i];wd[i]=wd[j];wd[j]=t;int x=wl[i];wl[i]=wl[j];wl[j]=x;}
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*t=m+7*s+3*b; if(t[0]=='-'){T[s][b][0]=-1;continue;} T[s][b][0]=t[0]-'0';T[s][b][1]=t[1]=='R'?1:-1;T[s][b][2]=t[2]-'A';}
  long long h=N/2,lo=h,hi=h; int st=0; long long cnt=0;
  for(long long k=1;k<=max;k++){
    int x=tape[h]; int*tr=T[st][x]; if(tr[0]<0){printf("HALT %lld\n",k);return 0;}
    tape[h]=tr[0]; h+=tr[1]; st=tr[2];
    int ev=0; if(h<lo){lo=h; if(side=='L'||side=='B')ev=1;} if(h>hi){hi=h; if(side=='R'||side=='B')ev=1;}
    if(ev && (cnt++%every==0)){
      printf("%lld %c ",k,h==lo?'L':'R');
      long long i=lo; const char*pt=NULL; int pc=0;
      #define FLUSH if(pt){ if(pc==1)printf("%s ",pt); else printf("%s^%d ",pt,pc);} pt=NULL;pc=0;
      while(i<=hi){
        if(i==h){FLUSH; printf("%c> ",'A'+st);}
        const char*tok=NULL; int L=1;
        for(int w=0;w<nw;w++){ if(i+wl[w]-1>hi) continue; int ok=1; for(int j=0;j<wl[w];j++){ if(tape[i+j]!=wd[w][j]-'0'||(j>0&&i+j==h)){ok=0;break;} } if(ok){tok=wn[w];L=wl[w];break;} }
        static char cs[2][2]={"0","1"}; if(!tok){tok=cs[tape[i]];L=1;}
        if(pt&&!strcmp(pt,tok))pc++; else {FLUSH; pt=tok;pc=1;}
        i+=L;
      }
      FLUSH; printf("\n");
    }
  }
  printf("END %lld\n",max); return 0;
}
