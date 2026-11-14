// own direct simulator. usage: sim TAPE maxsteps vfrom vto vevery
// TAPE: cells left of head ("-" for blank), head starts in A on the blank cell right of it.
// prints: V <visit#> <steps> <tape left of head>   for visits (state A entering a never-visited cell on the right)
//         L <steps> <state> <offset>                 when the head goes left of everything seen so far (first 200)
//         HALT <steps incl. halting transition> <state> <head offset from initial left edge> <tape> visits <n>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static const char *M="1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB";
int main(int c,char**v){
 static signed char W[12],Mv[12],Nx[12];
 for(int s=0;s<6;s++)for(int r=0;r<2;r++){const char*q=M+s*7+r*3; int k=s*2+r; if(q[0]=='-')Nx[k]=-1; else{W[k]=q[0]-'0';Mv[k]=q[1]=='R'?1:-1;Nx[k]=(q[2]-'A')*2;}}
 const char*tp=v[1]; unsigned long long mx=strtoull(v[2],0,10); long vf=atol(v[3]),vt=atol(v[4]),ve=atol(v[5]);
 long SZ=1L<<32; char*t=calloc(SZ,1); long L=strcmp(tp,"-")?strlen(tp):0; long base=SZ/2;
 for(long i=0;i<L;i++)t[base+i]=tp[i]-'0';
 long p=base+L,lo=base,hi=p-1; int s=0; unsigned long long n=0; long nv=0; int nl=0;
 for(;;){
  if(p>hi){hi=p; if(s==0){ if(L||n)nv++; if(nv>=vf&&nv<=vt&&(nv-vf)%ve==0){printf("V %ld %llu ",nv,n); long a=lo; while(a<p&&!t[a])a++; for(long i=a;i<p;i++)putchar('0'+t[i]); putchar(10);} } }
  if(p<lo){lo=p; if(nl<200){nl++; printf("L %llu %c %ld\n",n,'A'+s/2,p-base);} }
  if(n>=mx){printf("LIMIT %llu visits %ld lo %ld hi %ld\n",n,nv,lo-base,hi-base);break;}
  // inner loop: run while strictly inside (lo,hi) region, in chunks
  {
   char*q=t+p,*ql=t+lo,*qh=t+hi; int k; unsigned long long m=n; 
   do{ k=s+*q; if(Nx[k]<0)goto halt; *q=W[k]; q+=Mv[k]; s=Nx[k]; m++; }while(q>=ql&&q<=qh&&m<mx);
   p=q-t; n=m; continue;
   halt: p=q-t; n=m;
   printf("HALT %llu %c %ld ",n+1,'A'+s/2,p-base); long a=lo; while(a<hi&&!t[a])a++; if(hi-a<4000)for(long i=a;i<=hi;i++)putchar('0'+t[i]); else printf("len=%ld",hi-a+1); printf(" visits %ld\n",nv); break;
  }
 }
 return 0;}
