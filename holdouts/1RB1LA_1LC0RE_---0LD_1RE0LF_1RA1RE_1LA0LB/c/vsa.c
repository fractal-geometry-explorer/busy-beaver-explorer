// The maps G and GA of lean/Map.lean for 1RB1LA_1LC0RE_---0LD_1LA0LF_1RA1RE_1LA0LB (SIB = 0) and its sibling
// 1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LA0LB (SIB = 1), which differ in the rule for a block of one 1,
// with exact machine step counts, the transfer loop (top block K >= 4 against a 0 on the right) done at once.
// usage: vsa MAX_GA_STEPS SIB [v]     (this folder: SIB = 1); v prints every configuration
// "macro-steps" are applications of GA, "V-steps" the applications of G they stand for.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef uint64_t u64; typedef unsigned __int128 u128;
#define MAXL 1000000
static u64 gs[MAXL], bs[MAXL];
static void p128(u128 x){ char b[50]; int i=49; b[i]=0; if(!x)b[--i]='0'; while(x){b[--i]='0'+(int)(x%10); x/=10;} printf("%s",b+i); }
int main(int argc,char**argv){
  double N=atof(argv[1]); int sib=atoi(argv[2]);
  int ng=1,nb=0; gs[0]=1; u64 n=0,next=10,mac=0; u128 steps=1; u64 low=0; u128 vn=0;
  for(;;){
    if(ng==0||gs[ng-1]==0){printf("HALT: macro-step %llu, V-step ",(unsigned long long)n); p128(vn); printf(", machine steps before the halting transition "); p128(steps+1); printf("\n");return 0;}
    u64 k=gs[--ng];
    if(k==3){ if(nb) bs[nb-1]++; else bs[nb++]=1; bs[nb++]=0; steps+=4; }
    else {
      u64 b= nb? bs[--nb]:0;
      if(k==1){ u64 g= ng? gs[--ng]:0;
        if(sib){ if(ng) gs[ng-1]+=1; else gs[ng++]=1; gs[ng++]=g+b+4; steps+=2*g+b+13; }
        else { if(ng) gs[ng-1]+=2; else gs[ng++]=2; gs[ng++]=g+b+3; steps+=4*g+b+13; } }
      else if(k==2){ u64 g= ng? gs[--ng]:0; if(ng) gs[ng-1]+=1; else gs[ng++]=1; gs[ng++]=g+2; gs[ng++]=b+2; steps+=2*g+b+11; }
      else if(b==0){ u64 f=2+(k&1), j=(k-f)/2; // j rounds: K -= 2, next left += 1, next right += 1
        if(ng) gs[ng-1]+=j; else gs[ng++]=j; gs[ng++]=f;
        if(nb) bs[nb-1]+=j; else bs[nb++]=j; bs[nb++]=0;
        steps += (u128)2*k*j - (u128)2*j*(j-1) + (u128)15*j; vn += 2*j-1; }
      else { if(ng) gs[ng-1]+=1; else gs[ng++]=1; gs[ng++]=k-2; gs[ng++]=b+3; steps+=2*k+b+11; }
    }
    n++; vn++; if(ng<=1) low++;
    if(ng>MAXL-5||nb>MAXL-5){printf("overflow\n");return 1;}
    if(n==next||argc>3){ u64 tg=0,tb=0; for(int i=0;i<ng;i++)tg+=gs[i]; for(int i=0;i<nb;i++)tb+=bs[i];
      printf("macro-steps=%llu V-steps=",(unsigned long long)n); p128(vn); printf(" machine-steps="); p128(steps); printf(" ones=%llu left-blocks=%d right-blocks=%d top=%llu low=%llu\n",(unsigned long long)(tg+tb),ng,nb,(unsigned long long)(ng?gs[ng-1]:0),(unsigned long long)low); fflush(stdout); if(n==next){ static int ph=0; next = ph==0? next*2 : ph==1? next/2*5 : next*2; ph=(ph+1)%3; } if((double)n>=N) break; }
  }
  return 0;
}
