// iterate the proved node map F of 1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA from s 7
#include <stdio.h>
#include <stdlib.h>
typedef unsigned long long u64;
int main(int argc,char**argv){
  u64 maxret=atoll(argv[1]); int every=argc>2?atoi(argv[2]):1000000;
  int ty=0; u64 A=7,B=0; // ty 0:s x ; 1:p a m ; 2:q u c ; 3:t u v
  u64 rets=0, nsteps=0, sinceS=0, maxsince=0;
  while(rets<maxret){
    nsteps++; sinceS++;
    if(ty==0){ ty=1; B=A+6; A=0; rets++; if(sinceS>maxsince)maxsince=sinceS; sinceS=0; if(rets%every==0) printf("ret %llu X=%llu nodes=%llu maxsince=%llu\n",rets,B,nsteps,maxsince); fflush(stdout); continue;}
    if(ty==1){ u64 a=A,m=B;
      if(2*a+9<=m){A=2*a+6;B=m-(2*a+9);continue;}
      if(m==0){printf("HALT at ret %llu node p %llu 0\n",rets,a);return 0;}
      if(m==1){ if(a%2==0){ty=0;A=2*a+7;} else {ty=2;A=a/2+1;B=1;} continue;}
      if(m==2){ if(a%2==0){ty=3;A=a/2+1;B=0;} else {ty=0;A=2*a+9;} continue;}
      u64 z=(m-3)/2, r=(m-3)%2, pp=a+2-z;
      if(pp==0){ty=0;A=r==0?4*z+1:4*z+7;continue;}
      if(pp%2==1){u64 qq=pp/2; if(r==0){ty=1;A=2*qq+3;B=4*z+2;} else {ty=3;A=qq;B=2*z+2;} continue;}
      {u64 qq=pp/2-1; if(r==0){ty=2;A=qq;B=2*z+3;} else {ty=0;A=4*qq+4*z+11;} continue;}
    }
    if(ty==2){ u64 u=A,c=B;
      if(c>=4){ty=1;A=2*u+8;B=2*c-8;continue;}
      if(c==0){ty=0;A=4*u+11;} else if(c==1){ty=2;A=0;B=2*u+5;} else if(c==2){ty=1;A=3;B=4*u+10;} else {ty=0;A=4*u+13;}
      continue;}
    if(ty==3){ ty=2; B=2*A+B+5; A=0; continue;}
  }
  printf("done rets=%llu nodes=%llu\n",rets,nsteps);
}
