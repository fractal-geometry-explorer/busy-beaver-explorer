// G-map of 1RB1RA_1LC1LB_1RE0LD_1RA0LB_---0RF_1RC0RA with exact machine step counts (128-bit).
// usage: gs MAX_G_STEPS   prints at powers of ten and at halt
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef uint64_t u64; typedef unsigned __int128 u128;
#define MAXL 100000
static u64 fs[MAXL], rest[MAXL];
static void p128(u128 x){ char b[50]; int i=49; b[i]=0; if(!x)b[--i]='0'; while(x){b[--i]='0'+(int)(x%10); x/=10;} printf("%s",b+i); }
int main(int argc,char**argv){
  double N=atof(argv[1]);
  int nf=0,nr=0; u64 b=3; int mode=1; u64 n=0,next=10; u128 steps=8;
  for(;;){
    if(mode==0){
      if(b==0){printf("HALT: G-step %llu, machine steps before the halting transition ",(unsigned long long)n); p128(steps); printf("\n");return 0;}
      u64 c= nr? rest[--nr]:0; u64 j=(b-1)>>1; u64 b0=b-2*j; // rounds from b down to b0 (1 or 2)
      steps += (u128)2*b0*j + (u128)2*j*(j+1) + (u128)3*j;
      if(nf) fs[nf-1]+=j; else fs[nf++]=j;
      if(b&1){ fs[nf++]=2; b=c+j; steps+=3; } else { mode=1; b=c+j+3; steps+=10; }
    } else {
      if(!nf){ fs[nf++]=1; b++; mode=0; steps+=2; }
      else { u64 f=fs[--nf];
        if(f>=2){ rest[nr++]=b+1; b=f-2; steps+=f+1; }
        else if(f==1){ u64 h= nf? fs[--nf]:0; b=h+b+3; steps+=h+7; }
        else { if(nf) fs[nf-1]++; else fs[nf++]=1; b++; mode=0; steps+=2; }
      }
    }
    n++;
    if(nf+nr>MAXL-5){printf("overflow\n");return 1;}
    if(n==next||argc>2){ u64 t=b; for(int i=0;i<nf;i++)t+=fs[i]; for(int i=0;i<nr;i++)t+=rest[i];
      printf("G-steps=%llu machine-steps=",(unsigned long long)n); p128(steps); printf(" ones=%llu blocks=%d mode=%c nf=%d b=%llu\n",(unsigned long long)t,nf+nr+1,mode?'s':'e',nf,(unsigned long long)b); fflush(stdout); if(n==next){ static int ph=0; next = ph==0? next*2 : ph==1? next/2*5 : next*2; ph=(ph+1)%3; } if((double)n>=N) break; }
  }
  return 0;
}
