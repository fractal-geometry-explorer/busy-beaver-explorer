// own block-accelerated direct simulator (K cells per block), same interface/output as sim.c
// usage: sim2 TAPE maxsteps vfrom vto vevery     (maxsteps may be overshot by < one block traversal)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#ifndef K
#define K 16
#endif
static const char *M="1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB";
static signed char W[12],Mv[12],Nx[12];
typedef struct{uint16_t nv; uint8_t ns; uint8_t fl; uint32_t st;} E;   // fl: 0 exit left,1 exit right,2 slow(halt)
static E *T;
static uint16_t *t; static long base; // cell c -> block c>>4 (K=16), bit c&15
static inline int get(long c){return (t[c/K]>>(c%K))&1;}
static inline void put(long c,int b){ if(b)t[c/K]|=(1u<<(c%K)); else t[c/K]&=~(1u<<(c%K)); }
int main(int c,char**v){
 for(int s=0;s<6;s++)for(int r=0;r<2;r++){const char*q=M+s*7+r*3; int k=s*2+r; if(q[0]=='-')Nx[k]=-1; else{W[k]=q[0]-'0';Mv[k]=q[1]=='R'?1:-1;Nx[k]=(q[2]-'A')*2;}}
 long NV=1L<<K; T=malloc(sizeof(E)*6*2*NV);
 for(int s=0;s<6;s++)for(int side=0;side<2;side++)for(long val=0;val<NV;val++){
   unsigned x=val; int pos=side?K-1:0; int st=s*2; uint32_t n=0; E e; e.fl=2;
   while(n<1000000){ int k=st+((x>>pos)&1); if(Nx[k]<0)break; if(W[k])x|=1u<<pos; else x&=~(1u<<pos); pos+=Mv[k]; st=Nx[k]; n++; if(pos<0){e.fl=0;break;} if(pos>=K){e.fl=1;break;} }
   e.nv=x; e.ns=st; e.st=n; T[(s*2+side)*NV+val]=e; }
 const char*tp=v[1]; unsigned long long mx=strtoull(v[2],0,10); long vf=atol(v[3]),vt=atol(v[4]),ve=atol(v[5]);
 long NB=1L<<30; t=calloc(NB,2); long L=strcmp(tp,"-")?strlen(tp):0; base=NB/2*K;
 for(long i=0;i<L;i++)put(base+i,tp[i]-'0');
 long *VL=0; long nvl=0,ivl=0; if(c>6){FILE*f=fopen(v[6],"r"); VL=malloc(8*4000000); while(fscanf(f,"%ld",&VL[nvl])==1)nvl++; fclose(f);}
 long p=base+L,lo=base,hi=p-1; int s=0; unsigned long long n=0; long nv=0; int nl=0;
 for(;;){
  if(p>hi){hi=p; if(s==0){ if(L||n)nv++; int pr=0; if(VL){ if(ivl<nvl&&VL[ivl]==nv){pr=1;ivl++;} } else pr=(nv>=vf&&nv<=vt&&(nv-vf)%ve==0); if(pr){printf("V %ld %llu ",nv,n); long a=lo; while(a<p&&!get(a))a++; for(long i=a;i<p;i++)putchar('0'+get(i)); putchar(10);} } }
  if(p<lo){lo=p; if(nl<200){nl++; printf("L %llu %c %ld\n",n,'A'+s/2,p-base);} }
  if(n>=mx){printf("LIMIT %llu visits %ld lo %ld hi %ld\n",n,nv,lo-base,hi-base);break;}
  long b=p/K; int off=p%K;
  if((off==0||off==K-1) && b>lo/K && b<hi/K){
    // fast path
    long bl=lo/K,bh=hi/K; int side=off?1:0; int ss=s/2;
    for(;;){ E e=T[(ss*2+side)*NV+t[b]]; if(e.fl==2)break; t[b]=e.nv; n+=e.st; ss=e.ns/2; if(e.fl){b++;side=0;}else{b--;side=1;} if(b<=bl||b>=bh||n>=mx)break; }
    s=ss*2; p=b*K+(side?K-1:0);
    if(b>bl&&b<bh&&n<mx){ /* slow entry (halt inside block): fall through to single steps */ } else continue;
  }
  { int k=s+get(p); if(Nx[k]<0){
     printf("HALT %llu %c %ld ",n+1,'A'+s/2,p-base); long a=lo; while(a<hi&&!get(a))a++; if(hi-a<4000)for(long i=a;i<=hi;i++)putchar('0'+get(i)); else printf("len=%ld",hi-a+1); printf(" visits %ld\n",nv); break; }
    put(p,W[k]); p+=Mv[k]; s=Nx[k]; n++; }
 }
 return 0;}
