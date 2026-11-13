// round MACHINE PRE W ST MAXSTEPS < lines "T n": start 0^inf ST> 0 PRE W^n T 0^inf; next checkpoint of same form; print T' n' steps
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<24)
static unsigned char tape[N];
int main(int c,char**v){
  char*m=v[1]; char*PRE=v[2]; char*W=v[3]; int ST=v[4][0]-'A'; long long S=atoll(v[5]);
  int lw=strlen(W), lp=strlen(PRE);
  int w[6][2],d[6][2],ns[6][2];
  for(int i=0;i<6;i++)for(int b=0;b<2;b++){char*s=m+7*i+3*b; if(s[2]=='-'){ns[i][b]=-1;continue;} w[i][b]=s[0]-'0'; d[i][b]=s[1]=='R'?1:-1; ns[i][b]=s[2]-'A';}
  static char Z[100000]; long long n0;
  while(scanf("%s %lld",Z,&n0)==2){
    memset(tape,0,N);
    long long lo=N-1000000, p=lo+1; 
    for(int j=0;j<lp;j++) tape[p++]=PRE[j]-'0';
    for(long long i=0;i<n0;i++) for(int j=0;j<lw;j++) tape[p++]=W[j]-'0';
    if(strcmp(Z,"-")) for(char*q=Z;*q;q++) tape[p++]=*q-'0';
    long long pos=lo, hi=p; int st=ST; long long n; int done=0;
    for(n=1;n<=S;n++){
      int b=tape[pos]; int t=ns[st][b]; if(t<0){printf("%s %lld HALT %lld\n",Z,n0,n);done=1;break;}
      tape[pos]=w[st][b]; pos+=d[st][b]; st=t;
      if(pos>hi)hi=pos;
      if(pos<lo){lo=pos; if(st==ST){
        int ok=1; for(int j=0;j<lp;j++) if(tape[lo+1+j]!=PRE[j]-'0') {ok=0;break;}
        if(!ok) continue;
        long long e=lo+1+lp, k=0;
        while(1){ int g=1; for(int j=0;j<lw;j++) if(tape[e+j]!=W[j]-'0'){g=0;break;} if(!g)break; e+=lw;k++; }
        if(k<8) continue;
        long long a=hi; while(a>=e&&tape[a]==0)a--;
        if(a-e>400) continue;
        printf("%s %lld -> ",Z,n0); if(a<e)putchar('-'); for(long long i=e;i<=a;i++)putchar(48+tape[i]); printf(" %lld %lld\n",k,n); done=1; break;
      }}
    }
    if(!done) printf("%s %lld TIMEOUT\n",Z,n0);
    fflush(stdout);
  }
}
