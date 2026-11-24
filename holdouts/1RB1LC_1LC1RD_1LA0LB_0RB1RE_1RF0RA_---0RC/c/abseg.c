/* abseg.c: one segment of the A(a,b) orbit of 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC, one visit at a time with the
   full rules (as abrun.c), and the exact number of machine steps of the segment in 256-bit arithmetic.

   usage: abseg i0 a0 b0 n
   Runs n visits from visit i0 = A(a0, b0) (or until the halt) and prints
       seg i0=... a0=... b0=... i1=... a1=... b1=... dT=...        (dT: machine steps from visit i0 to visit i1)
   or, when the halting rule fires at visit h,
       seg ... HALT h=... a=... dT=...                             (dT: steps from visit i0 to the halt, its 11 included)
   Chaining segments from A(2, 9) (52 steps from blank tape) and adding the dT gives the exact step count.
   The grow/swap choice is branch-free (cmov); the resets are rare branches. */
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
typedef unsigned long long u64;

static void pr(u128 x){char s[50];int i=49;s[i]=0;if(!x){fputs("0",stdout);return;}while(x){s[--i]='0'+(int)(x%10);x/=10;}fputs(s+i,stdout);}
/* 256-bit number hi*2^128 + lo, printed in decimal */
static void pr256(u128 hi, u128 lo){
  if(!hi){pr(lo);return;}
  /* repeated division by 10^18 of a 4-limb number */
  u64 w[4]={(u64)lo,(u64)(lo>>64),(u64)hi,(u64)(hi>>64)}; char buf[100]; int n=0;
  for(;;){ int z=1; for(int k=0;k<4;k++) if(w[k]) z=0; if(z) break;
    u128 r=0; for(int k=3;k>=0;k--){ u128 cur=(r<<64)|w[k]; w[k]=(u64)(cur/1000000000000000000ULL); r=cur%1000000000000000000ULL; }
    u64 rr=(u64)r; for(int t=0;t<18;t++){ buf[n++]='0'+rr%10; rr/=10; } }
  while(n>1 && buf[n-1]=='0') n--;
  while(n) putchar(buf[--n]);
}

int main(int argc,char**argv){
  if(argc<5){fprintf(stderr,"usage: abseg i0 a0 b0 n\n");return 1;}
  u64 i0=strtoull(argv[1],0,10), a0=strtoull(argv[2],0,10), b0=strtoull(argv[3],0,10), n=strtoull(argv[4],0,10);
  u64 a=a0,b=b0; u128 lo=0,hi=0; u64 i=i0, end=i0+n; int halted=0;
  for(;i<end;i++){
    u128 c;
    u64 d=b-a;   /* as unsigned: small only when b > a and b - a is small */
    if(b<=3 || (b>a && d<=3)){
      if(b==3){ c=11; lo+=c; if(lo<c) hi++; halted=1; break; }
      else if(b==2){ c=25; a-=3; b=7; }
      else if(d==1){ c=(u128)2*a*a+5*a+7; b=2*a+4; a=4; }
      else if(d==2){ c=(u128)2*a*a+9*a+23; b=2*a+7; a=1; }
      else if(a&1){ c=(u128)2*a*a+12*a+39; a=2*a+1; b=9; }
      else { c=(u128)2*a*a+12*a-1; b=b-a-1; a=2*a+4; }  /* d == 3, a even: grow, then b = 2 */
    } else {
      /* swap if a >= b, else grow (a even: +4/-1, a odd: +3/0) */
      int sw = a>=b; u64 od=a&1;
      u128 cg=(u128)2*a*a+12*a-1+14*od;           /* grow cost */
      u128 cs=(u128)2*b*b+b+5;                     /* swap cost */
      u64 ga=2*a+4-od, gb=b-a-1+od;                /* grow target */
      u64 sa=a-b+1, sb=2*b+3;                      /* swap target */
      c = sw? cs: cg; a = sw? sa: ga; b = sw? sb: gb;
    }
    lo+=c; if(lo<c) hi++;
  }
  printf("seg i0=%llu a0=%llu b0=%llu ",i0,a0,b0);
  if(halted){ printf("HALT h=%llu a=%llu dT=",i,a); pr256(hi,lo); printf("\n"); }
  else { printf("i1=%llu a1=%llu b1=%llu dT=",i,a,b); pr256(hi,lo); printf("\n"); }
  return 0;
}
