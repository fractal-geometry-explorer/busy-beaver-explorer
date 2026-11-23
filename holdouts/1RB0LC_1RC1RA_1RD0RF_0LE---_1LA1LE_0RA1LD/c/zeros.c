#include <stdio.h>
#include <stdlib.h>
// zeros.c: does the tape of 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD ever hold 000 away from the head?
// usage: zeros TO EVERY   direct run from blank tape; every EVERY steps, count the runs of three or more 0s strictly
//        inside the visited tape and more than 8 cells from the head, and print the first few and a total.
// build: gcc -O2 -o zeros zeros.c
int main(int argc,char**argv){
 const char*m="1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD"; int W[6][2],D[6][2],N[6][2];
 for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*x=m+7*s+3*b; if(x[0]=='-'){N[s][b]=-1;continue;} W[s][b]=x[0]-'0';D[s][b]=x[1]=='R'?1:-1;N[s][b]=x[2]-'A';}
 long long to=atoll(argv[1]),ev=atoll(argv[2]);
 long long S=1LL<<27; unsigned char*t=calloc(S,1); long long p=S/2,lo=p,hi=p; int st=0; long long hits=0,samples=0,maxz=0;
 for(long long k=1;k<=to;k++){ int b=t[p]; int ns=N[st][b]; if(ns<0){printf("HALT %lld\n",k);return 0;} t[p]=W[st][b]; p+=D[st][b]; st=ns;
  if(p<lo)lo=p; if(p>hi)hi=p;
  if(k%ev==0){ samples++; long long i=lo; while(i<=hi&&!t[i])i++; long long c=0,mz=0; while(i<=hi){ long long z0=i; while(i<=hi&&!t[i])i++; long long z=i-z0; if(i<=hi&&z>=3&&(p<z0-8||p>i+8)){c++; if(z>mz)mz=z; if(c<=2 && hits<20) printf("step %lld z%lld at %lld (head %lld) len %lld\n",k,z,z0-lo,p-lo,hi-lo);} while(i<=hi&&t[i])i++; }
   if(c){hits++;} if(mz>maxz)maxz=mz; }
 } printf("samples %lld with interior 000: %lld, longest %lld\n",samples,hits,maxz); return 0;}
