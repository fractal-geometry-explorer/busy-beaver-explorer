/* abrun.c: iterate the A(a,b) rules of 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC from A(2,9) in 128-bit integers.
   Logs every "near" visit with 1 <= b - a <= 8 (b > a) and every reset rule, and the exact machine step count.
   usage: abrun N [logevery]   */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
static void pr(FILE*f,u128 x){char s[50];int i=49;s[i]=0;if(!x){fputs("0",f);return;}while(x){s[--i]='0'+(int)(x%10);x/=10;}fputs(s+i,f);}
int main(int argc,char**argv){
  unsigned long long N=strtoull(argv[1],0,10), LE=argc>2?strtoull(argv[2],0,10):0;
  u128 a=2,b=9,T=52; unsigned long long cnt[8]={0}; const char*nm[8]={"ge","de","do","p1","p2","p3","b2","H"};
  unsigned long long near[9][2]; memset(near,0,sizeof near);
  u128 LIM=((u128)1)<<100;
  for(unsigned long long i=0;i<N;i++){
    if(b>a && b-a<=8){ int g=(int)(b-a); near[g][(int)(a&1)]++;
      printf("near i=%llu g=%d par=%d a=",i,g,(int)(a&1)); pr(stdout,a); printf(" T="); pr(stdout,T); printf("\n"); fflush(stdout);}
    int r;
    if(b==3){ printf("HALT at i=%llu a=",i); pr(stdout,a); printf(" T="); pr(stdout,T+11); printf("\n"); cnt[7]++; break; }
    else if(b==2){ T+=25; a-=3; b=7; r=6; }
    else if(a>=b){ T+=2*b*b+b+5; a=a-b+1; b=2*b+3; r=0; }
    else if(b==a+1){ T+=2*a*a+5*a+7; b=2*a+4; a=4; r=3; }
    else if(b==a+2){ T+=2*a*a+9*a+23; b=2*a+7; a=1; r=4; }
    else if((a&1) && b==a+3){ T+=2*a*a+12*a+39; a=2*a+1; b=9; r=5; }
    else if(!(a&1)){ T+=2*a*a+12*a-1; b=b-a-1; a=2*a+4; r=1; }
    else { T+=2*a*a+12*a+13; b=b-a; a=2*a+3; r=2; }
    cnt[r]++;
    if(a>LIM||b>LIM){printf("overflow guard at i=%llu\n",i);break;}
    if(LE && (i+1)%LE==0){ printf("prog i=%llu a=",i+1); pr(stdout,a); printf(" b="); pr(stdout,b); printf(" T="); pr(stdout,T); printf("\n"); fflush(stdout);}
  }
  printf("final a="); pr(stdout,a); printf(" b="); pr(stdout,b); printf(" T="); pr(stdout,T); printf("\n");
  for(int k=0;k<8;k++) printf("%s %llu\n",nm[k],cnt[k]);
  for(int g=1;g<=8;g++) printf("near g=%d even %llu odd %llu\n",g,near[g][0],near[g][1]);
}
