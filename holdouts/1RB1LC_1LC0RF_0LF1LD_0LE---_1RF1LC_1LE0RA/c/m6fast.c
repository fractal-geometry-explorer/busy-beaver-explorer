// m6fast: run 1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA from blank tape, jumping over the rounds
// 0^inf F> 0 0 (110)^x 1^(y+5) R -> 0^inf F> 0 0 (110)^(x+2) 1^(y+1) R (12x+26 steps, Lean: round/rounds).
// usage: m6fast PHASES [TAPESIZE [L TAIL [FORM]]]
//   without L: from blank tape; with L: from a phase start  0^inf C> 0 1^L T 0^inf  (FORM 1: 0 10 1^(L-2) T), T given
//   as a comma list of block lengths b1,b2,... meaning 0 1^b1 0 1^b2 ...
// Prints each phase start (head in C on a new left cell, then 1^l or 10 1^(l-2), l >= 5): index, steps, l, form
// ("a" = 10 1^(l-2)), and the tail after the ones as the same comma list.  Steps are exact (128-bit): the jumped
// rounds are counted with their step counts from the Lean rule.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
static unsigned char *t; static long SZ;
static void pr128(u128 v){char b[50];int i=49;b[i]=0;if(!v){putchar('0');return;}while(v){b[--i]='0'+(int)(v%10);v/=10;}fputs(b+i,stdout);}
int main(int argc,char**argv){
  const char*m="1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA";
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){const char*x=m+s*7+r*3; if(x[0]=='-'){ns[s][r]=-1;continue;} nw[s][r]=x[0]-'0'; mv[s][r]=x[1]=='R'?1:-1; ns[s][r]=x[2]-'A';}
  int K=atoi(argv[1]); SZ=argc>2?atol(argv[2]):(1L<<31); long L0=argc>3?atol(argv[3]):0; const char*TL=argc>4?argv[4]:""; int F0=argc>5?atoi(argv[5]):0;
  t=calloc(SZ,1); if(!t){puts("nomem");return 1;}
  long p=SZ-(SZ/64), lo=p, hi=p; int st=0;
  if(L0){ st=2; long q=p+1; if(F0){t[q++]=1;t[q++]=0;L0-=2;} for(long i=0;i<L0;i++)t[q++]=1; const char*c=TL; while(*c){ long b=atol(c); t[q++]=0; for(long i=0;i<b;i++)t[q++]=1; while(*c&&*c!=',')c++; if(*c)c++; } hi=q-1; } u128 steps=0; int got=0;
  setvbuf(stdout,NULL,_IONBF,0);
  while(got<K){
    int r=t[p]; int n=ns[st][r]; if(n<0){printf("HALT steps ");pr128(steps);printf(" pos %ld\n",p-lo);return 0;}
    t[p]=nw[st][r]; p+=mv[st][r]; st=n; steps++;
    if(p>hi) hi=p;
    if(p<lo){ lo=p;
      if(st==2 && t[p+1]==1){ long i=p+1,n1=0,form=0; if(t[p+2]==0){form=1;i=p+3;} while(t[i]==1){n1++;i++;}
        if(n1>=5){ printf("%d ",got+1); pr128(steps); printf(" %ld %s ",n1+(form?2:0),form?"a":"-");
          long z=0; for(;i<=hi;i++){ if(t[i]==0){ if(z) printf("%ld,",z-1); z=1;} else if(z) z++; else putchar('?'); } if(z) printf("%ld",z-1); putchar('\n'); got++; }}
      if(st==5 && t[p]==0 && t[p+1]==0){ // F> 0 0 (110)^x 1^y R ?
        long i=p+2,x=0; while(t[i]==1&&t[i+1]==1&&t[i+2]==0){x++;i+=3;} long y=0; while(t[i+y]==1) y++;
        if(y>=5){ long k=(y-1)/4; // k rounds
          long np=p-2*k; if(np<1000){puts("OUT");return 1;}
          long j=np; t[j++]=0; t[j++]=0; for(long w=0;w<x+2*k;w++){t[j++]=1;t[j++]=1;t[j++]=0;} for(long w=0;w<y-4*k;w++) t[j++]=1;
          // j should equal i+y
          if(j!=i+y){printf("BUG %ld %ld\n",j,i+y);return 1;}
          steps += (u128)k*(12*(u128)x+26) + (u128)12*2*((u128)k*(k-1)/2);
          p=np; lo=np; }
      }
    }
    if(p<1000||p>SZ-1000){printf("OUT\n");return 0;}
  }
  return 0;}
