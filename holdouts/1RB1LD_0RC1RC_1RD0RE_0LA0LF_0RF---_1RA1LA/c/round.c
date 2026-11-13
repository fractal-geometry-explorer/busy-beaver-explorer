// round MACHINE W SUF ST MAXSTEPS < lines "Z n" : start 0^inf Z W^n SUF ST> 0^inf ; run to next checkpoint of same form; print Z' n' steps
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<24)
static unsigned char tape[N];
int main(int c,char**v){
  char*m=v[1]; char*W=v[2]; char*SUF=v[3]; int ST=v[4][0]-'A'; long long S=atoll(v[5]);
  int lw=strlen(W), ls=strlen(SUF);
  int w[6][2],d[6][2],ns[6][2];
  for(int i=0;i<6;i++)for(int b=0;b<2;b++){char*s=m+7*i+3*b; if(s[2]=='-'){ns[i][b]=-1;continue;} w[i][b]=s[0]-'0'; d[i][b]=s[1]=='R'?1:-1; ns[i][b]=s[2]-'A';}
  static char Z[100000]; long long n0;
  while(scanf("%s %lld",Z,&n0)==2){
    memset(tape,0,N);
    long long lo=N/2, p=lo; 
    if(strcmp(Z,"-")) for(char*q=Z;*q;q++) tape[p++]=*q-'0';
    for(long long i=0;i<n0;i++) for(int j=0;j<lw;j++) tape[p++]=W[j]-'0';
    for(int j=0;j<ls;j++) tape[p++]=SUF[j]-'0';
    long long pos=p, hi=p; int st=ST; long long n; int done=0;
    for(n=1;n<=S;n++){
      int b=tape[pos]; int t=ns[st][b]; if(t<0){printf("%s %lld HALT %lld\n",Z,n0,n);done=1;break;}
      tape[pos]=w[st][b]; pos+=d[st][b]; st=t;
      if(pos<lo)lo=pos;
      if(pos>hi){hi=pos; if(st==ST){
        // check suffix
        int ok=1; for(int j=0;j<ls;j++) if(tape[hi-ls+j]!=SUF[j]-'0') {ok=0;break;}
        if(!ok) continue;
        long long e=hi-ls, k=0;
        while(e-lw>=lo){ int g=1; for(int j=0;j<lw;j++) if(tape[e-lw+j]!=W[j]-'0'){g=0;break;} if(!g)break; e-=lw;k++; }
        if(k<8) continue;
        long long a=lo; while(a<e&&tape[a]==0)a++;
        if(e-a>300) continue;
        printf("%s %lld -> ",Z,n0); if(e==a)putchar('-'); for(long long i=a;i<e;i++)putchar(48+tape[i]); printf(" %lld %lld\n",k,n); done=1; break;
      }}
    }
    if(!done) printf("%s %lld TIMEOUT\n",Z,n0);
    fflush(stdout);
  }
}
