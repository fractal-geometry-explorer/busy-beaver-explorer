// Direct check of the regular model (used by py/validate.py). stdin: MACHINE STEPS HEAD STATE TAPE.
// Runs STEPS steps, counts the Q events (B reading 0 after 1^m, m % 3 == 0, with a 0 before the run) and prints
// the count, the step of the last one and that configuration (W blocks, m, R gaps); or HALT / OUT.
#include <stdio.h>
#include <stdlib.h>
int Wt[6][2],Mv[6][2],St[6][2];
void parse(const char*s){for(int i=0;i<6;i++)for(int b=0;b<2;b++){const char*x=s+7*i+3*b; if(x[2]=='-'){St[i][b]=-1;continue;} Wt[i][b]=x[0]-'0';Mv[i][b]=x[1]=='R'?1:-1;St[i][b]=x[2]-'A';}}
int main(){
  static char mach[64]; long long maxs, head; char stc;
  if(scanf("%63s %lld %lld %c",mach,&maxs,&head,&stc)!=4) return 1; parse(mach);
  size_t cap=1<<20,len=0; char*s=malloc(cap); int ch;
  while((ch=getchar())!=EOF){ if(ch=='0'||ch=='1'){ if(len==cap){cap*=2;s=realloc(s,cap);} s[len++]=ch; } }
  long long MARG=4000000, N=len+2*MARG; unsigned char*t=calloc(N,1);
  for(size_t i=0;i<len;i++) t[MARG+i]=s[i]-'0';
  long long pos=MARG+head, lo=MARG, hi=MARG+len-1; int st=stc-'A'; long long n=0, cnt=0, last=-1, fc=0;
  unsigned char*snap=malloc(N); long long slo=0,shi=0,spos=0;
  for(;n<maxs;n++){
    int sym=t[pos];
    if(st==0&&sym==1) fc++;
    if(St[st][sym]<0){ printf("HALT %lld\n",n+1); return 0; }
    if(st==1&&sym==0&&t[pos-1]==1){ long long m=0; while(t[pos-1-m]) m++; if(m%3==0 && t[pos-1-m]==0){ cnt++; last=n; slo=lo; shi=hi; spos=pos; } }
    t[pos]=Wt[st][sym]; pos+=Mv[st][sym]; st=St[st][sym];
    if(pos<lo)lo=pos; if(pos>hi)hi=pos; if(pos<5||pos>N-5){printf("OUT\n");return 0;}
  }
  printf("COUNT %lld LAST %lld F %lld\n",cnt,last,fc);
  // re-run to the last Q event to dump it (cheap: just rerun)
  for(size_t i=0;i<N;i++) t[i]=0; for(size_t i=0;i<len;i++) t[MARG+i]=s[i]-'0';
  pos=MARG+head; lo=MARG; hi=MARG+len-1; st=stc-'A';
  for(n=0;n<last;n++){ int sym=t[pos]; t[pos]=Wt[st][sym]; pos+=Mv[st][sym]; st=St[st][sym]; if(pos<lo)lo=pos; if(pos>hi)hi=pos; }
  long long m=0; while(t[pos-1-m]) m++; long long sep=pos-1-m;
  long long a=lo; while(t[a]==0) a++; printf("W"); long long c=0;
  for(long long x=a;x<sep;x++){ if(t[x]) c++; else { printf(" %lld",c); c=0; } } printf(" %lld\nM %lld\nR",c,m);
  long long g=0; for(long long x=pos+1;x<=hi;x++){ if(t[x]){ printf(" %lld",g); g=0;} else g++; } printf("\n");
  return 0;
}
