// 1RB0RF_1LC0RC_0LD1LC_1RE1LB_1RF---_1LE1RA from blank tape, with the transfer rule applied in closed form.
//
// Transfer rule (Lean: transfer, lean/Rules.lean), G = 0^inf 1^3 0 1 0 1^2 0 C> 0 (the left end of the tape):
//   G (1010)^j 10 1^3 R  ->  G (1010)^(j+1) 10 1 R      in 28j+64 steps, the tape grows by two cells on the left.
// Applied n = (m-1)/2 times to G (1010)^j 10 1^m it costs 28(nj + n(n-1)/2) + 64n steps; the plain machine needs
// about 3.5 m^2 steps for it, which is nearly all of its running time.
//
// usage: transfer MAXSTEPS(decimal, may exceed 2^64) MAXSECONDS [MINN] [plain]
//   prints a line for each application with n >= MINN (default 20): step, n, j, m, tape width, the 32 cells after
//   the block of ones;
//   "plain": never apply the rule (for checking); in both modes every configuration G ... is printed with a hash
//   of the tape when CHECK=1 is in the environment, so the two runs can be compared.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
typedef unsigned __int128 u128;
static void pr(u128 x){char b[50];int i=49;b[i]=0;if(!x)b[--i]='0';while(x){b[--i]='0'+(int)(x%10);x/=10;}fputs(b+i,stdout);}
static u128 rd(const char*s){u128 x=0;for(;*s>='0'&&*s<='9';s++)x=x*10+(*s-'0');return x;}
int main(int argc,char**argv){
 u128 maxs=rd(argv[1]);double maxt=atof(argv[2]);long minn=argc>3?atol(argv[3]):20;int plain=argc>4;
 int check=getenv("CHECK")!=NULL;
 // A0 1RB A1 0RF B0 1LC B1 0RC C0 0LD C1 1LC D0 1RE D1 1LB E0 1RF E1 --- F0 1LE F1 1RA
 static const int W[6][2]={{1,0},{1,0},{0,1},{1,1},{1,-1},{1,1}},Mv[6][2]={{1,1},{-1,1},{-1,-1},{1,-1},{1,0},{-1,1}},
  Q[6][2]={{1,5},{2,2},{3,2},{4,1},{5,-1},{4,0}};
 long N=1L<<33;unsigned char*t=calloc(N,1);if(!t){fprintf(stderr,"no memory\n");return 1;}
 long pos=N/2,lo=pos,hi=pos;int q=0;u128 st=0;clock_t c0=clock();long it=0;long jumps=0;
 static const unsigned char G[9]={1,1,1,0,1,0,1,1,0};
 while(st<maxs){
  if(q==2&&t[pos]==0&&pos-9==lo&&memcmp(t+lo,G,9)==0&&t[lo-1]==0){
   long p=pos+1,j=0;while(t[p]==1&&t[p+1]==0&&t[p+2]==1&&t[p+3]==0)p+=4,j++;
   long m=0,n=0;
   if(t[p]==1&&t[p+1]==0){long r=p+2;while(r<=hi&&t[r]==1)r++;m=r-(p+2);}
   if(check){unsigned long h=1469598103934665603UL;for(long i=lo;i<=hi;i++)h=(h^t[i])*1099511628211UL;
    printf("G ");pr(st);printf(" %lx\n",h);}
   if(!plain&&m>=3){
    n=(m-1)/2;long m2=m-2*n;
    st+=(u128)28*((u128)n*j+(u128)n*(n-1)/2)+(u128)64*n;
    long e=p+2+m; // one past the ones
    lo-=2*n;if(lo<16){fprintf(stderr,"tape\n");return 1;}
    memcpy(t+lo,G,9);t[lo+9]=0;
    for(long i=lo+10;i<e-m2;i+=2){t[i]=1;t[i+1]=0;}
    pos=lo+9;jumps++;
    if(n>=minn){printf("T ");pr(st);printf(" n=%ld j=%ld m=%ld width=%ld next=",n,j,m,hi-lo+1);
     for(long i=e;i<e+32&&i<=hi;i++)putchar('0'+t[i]);putchar('\n');fflush(stdout);}
    continue;}
  }
  int b=t[pos];if(Mv[q][b]==0){printf("HALT ");pr(st+1);printf("\n");return 0;}
  t[pos]=W[q][b];pos+=Mv[q][b];q=Q[q][b];st++;
  if(pos<lo)lo=pos;if(pos>hi)hi=pos;
  if(pos<16||pos>=N-16){fprintf(stderr,"tape\n");return 1;}
  if(!(++it&0xffffff)&&(double)(clock()-c0)/CLOCKS_PER_SEC>maxt)break;
 }
 printf("END ");pr(st);printf(" width=%ld jumps=%ld state=%c\n",hi-lo+1,jumps,'A'+q);return 0;}
