// Direct simulation of a transient of the family 1RB?RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_X--- (used by py/hyb.py).
// stdin: MACHINE MAXSTEPS HEAD STATE TAPE (a 0/1 string; HEAD an index into it, may be one past the end).
// Runs until the first regular Q event after at least one step:  W 0 1^m B>0 R  with m % 3 == 0, W a word
// (blocks of 1s separated by single 0s, blank to the left, at least two blocks, all but the first odd), R anything.
// Prints "F step ctx:..." for each time state A reads a 1 (the first 50), then "Q steps Fcount m", "W blocks...",
// "R gaps..." ; or "HALT steps" (bbchallenge count), "MAX", "OUT".
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int Wt[6][2],Mv[6][2],St[6][2];
void parse(const char*s){for(int i=0;i<6;i++)for(int b=0;b<2;b++){const char*x=s+7*i+3*b; if(x[2]=='-'){St[i][b]=-1;continue;} Wt[i][b]=x[0]-'0';Mv[i][b]=x[1]=='R'?1:-1;St[i][b]=x[2]-'A';}}
int main(){
  static char mach[64]; long long maxs; long long head; char stc; 
  if(scanf("%63s %lld %lld %c",mach,&maxs,&head,&stc)!=4) return 1;
  parse(mach);
  // read tape string
  size_t cap=1<<20, len=0; char*s=malloc(cap); int ch;
  while((ch=getchar())!=EOF){ if(ch=='0'||ch=='1'){ if(len==cap){cap*=2;s=realloc(s,cap);} s[len++]=ch; } }
  long long MARG=1000000; long long N=len+2*MARG;
  unsigned char*t=calloc(N,1);
  for(size_t i=0;i<len;i++) t[MARG+i]=s[i]-'0';
  long long pos=MARG+head, lo0=MARG, lo=MARG, hi=MARG+len-1; if(pos>hi)hi=pos; int st=stc-'A';
  long long n=0;  long long fcount=0;
  while(n<maxs){
    int sym=t[pos];
    if(st==0&&sym==1){ fcount++; if(fcount<=50){ printf("F %lld ctx:",n); for(long long i=pos-3;i<=pos+12&&i<N;i++) printf("%d",t[i]); printf("\n"); } }
    if(St[st][sym]<0){ printf("HALT %lld\n",n+1); return 0; }
    if(n>0 && st==1 && sym==0 && t[pos-1]==1){
      long long m=0; while(t[pos-1-m]) m++;
      if(m%3==0){
        long long sep=pos-1-m; int ok = (t[sep]==0);
        // left side: word, blocks after the first odd
        long long j=sep-1; int nb=0; long long b=0;
        if(ok){ if(t[j]==0) ok=0; }
        while(ok && j>=lo){ if(t[j]) b++; else { if(b==0){ long long z=j; while(z>=lo && t[z]==0) z--; if(z>=lo) ok=0; break; }
                if(b%2==0) ok=0; nb++; b=0; } j--; }
        if(b>0) nb++;
        if(ok && nb>=2){
          printf("Q %lld %lld %lld\n", n, fcount, m);
          long long a=lo; while(t[a]==0) a++; printf("W"); long long c=0;
          for(long long x=a;x<sep;x++){ if(t[x]) c++; else { printf(" %lld",c); c=0; } } printf(" %lld\n",c);
          printf("R"); long long g=0; for(long long x=pos+1;x<=hi;x++){ if(t[x]){ printf(" %lld",g); g=0;} else g++; } printf("\n");
          return 0;
        }
      }
    }
    t[pos]=Wt[st][sym]; pos+=Mv[st][sym]; st=St[st][sym]; n++;
    if(pos<lo){ lo=pos; } if(pos>hi) hi=pos;
    if(pos<10||pos>N-10){ printf("OUT\n"); return 0; }
  }
  printf("MAX %lld\n", n); return 0;
}
