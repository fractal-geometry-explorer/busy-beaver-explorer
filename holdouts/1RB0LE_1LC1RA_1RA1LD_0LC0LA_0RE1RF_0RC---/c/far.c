// Iterate DeepMind's map for 1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC--- far, with the sweep jumped, and watch the
// halting criterion of lean/Criterion.lean (halts_iff_visits): the machine halts iff the orbit visits some C(3B+1, k, B).
// The map is the one proved in lean/DMMap.lean.  t counts machine steps with the step counts of the rules in
// lean/DMRules.lean (from blank tape: 2 steps to C(0,0,2)); n counts steps of DeepMind's map.
// usage: gcc -O2 -o far far.c && ./far SECONDS
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
typedef unsigned long long u64;
int main(int argc,char**argv){
  double budget=atof(argv[1]);
  u64 m=0,k=0,b=2, walls=0, starts=0, near=0;
  long double n=0, t=2, heur=0; static u64 dec[200];  // heur: sum over sweep starts of 1/(B+1), a size scale for "chance" hits
  time_t t0=time(0), lastp=t0;
  for(;;){
    if(b>=1 && m>=3){
      long long d=(long long)m-3*(long long)b; starts++;
      if(d>=-1 && d<=3){ near++; if(near<=60) printf("near miss d=M-3B=%lld at sweep start M=%llu B=%llu (n=%.3Le t=%.3Le)\n",d,m,b,n,t); }
      if(d==1){printf("HALT CRITERION n=%.4Le t=%.4Le M=%llu B=%llu\n",n,t,m,b);return 0;}
      if(d>=-99 && d<=101){ int e=0; long double x=t; while(x>=10){x/=10;e++;} dec[e]++; }
      heur += 1.0L/(long double)(b+1);
      u64 j = m/3 < b ? m/3 : b;
      t += (long double)j*(6.0L*k+9) + 6.0L*j*(j-1); m-=3*j; k+=2*j; b-=j; n+=j; continue;
    }
    if(b==0){ t+=4.0L*k+3; m=m+1; b=2*k+2; k=0; n+=1; walls++;
      if((walls&0xFFFFF)==0){ time_t now=time(0); if(now-lastp>=60){ lastp=now;
        printf("n=%.4Le walls=%llu starts=%llu t=%.4Le m=%llu b=%llu sum1/B=%.4Lf el=%lds\n",n,walls,starts,t,m,b,heur,(long)(now-t0)); fflush(stdout);
        if(now-t0>budget) break; } }
      if(m>(1ULL<<60)||b>(1ULL<<60)){printf("overflow guard\n");break;}
      continue; }
    if(m==0){ if(b==1){t+=4.0L*k+7; m=2*k+3; k=0; b=2;} else {t+=4.0L*k+8; m=2*k+2; k=1; b-=2;} }
    else if(m==1){ if(k==0){t+=4; m=0; b+=2;} else if(b==1){t+=4.0L*k+33; m=2*k+5;k=0;b=2;} else {t+=4.0L*k+34; m=2*k+4;k=1;b-=2;} }
    else { if(k==0){ if(b==1){t+=8; m=0;k=1;b=0;} else {printf("HALT n=%.3Le t=%.3Le\n",n,t); return 0;} }
      else if(k==1){t+=10; m=0;} else if(b==1){t+=4.0L*k+17; m=2*k+3;k=0;b=2;} else {t+=4.0L*k+18; m=2*k+2;k=1;b-=2;} }
    n+=1;
  }
  for(int e=0;e<200;e++) if(dec[e]) printf("t in [1e%d,1e%d): %llu sweep starts with |M-3B-1|<=100\n",e,e+1,dec[e]);
  printf("END n=%.4Le t=%.4Le walls=%llu sweep starts=%llu near misses=%llu m=%llu k=%llu b=%llu\n",n,t,walls,starts,near,m,k,b);
}
