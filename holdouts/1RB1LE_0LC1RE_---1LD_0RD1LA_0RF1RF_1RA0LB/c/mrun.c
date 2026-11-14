// fast exact macro simulator: 16-cell blocks, full lookup table.
// usage: mrun MACHINE maxsteps SIDE(L|R|N) gap dump [ckpt_every]
// events: head enters the outermost-ever block on SIDE after >= gap steps since last time there.
// prints: EV step state(entering) blockidx(relative) and `dump` blocks of tape from that edge (cells as 0/1)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define K 16
#define NB (1<<K)
typedef unsigned long long u64;
int W[6][2],Mv[6][2],Nx[6][2];
typedef struct { uint16_t nb; uint8_t ns; uint8_t out; uint32_t st; } Ent; // out:0 left,1 right,2 halt,3 loop
Ent *T;
void build(){ T=malloc(sizeof(Ent)*6*2*NB);
 for(int s=0;s<6;s++)for(int side=0;side<2;side++)for(int b=0;b<NB;b++){
  // cell i (0=leftmost) is bit (K-1-i)
  int p=side?K-1:0; unsigned t=b; int st=s; uint32_t n=0; Ent e; 
  for(;;){ int r=(t>>(K-1-p))&1; if(Nx[st][r]<0){e.out=2;break;}
   if(W[st][r]) t|=1u<<(K-1-p); else t&=~(1u<<(K-1-p));
   int m=Mv[st][r]; st=Nx[st][r]; p+=m; n++;
   if(p<0){e.out=0;break;} if(p>=K){e.out=1;break;}
   if(n>50000000){e.out=3;break;} }
  e.nb=t;e.ns=st;e.st=n; T[(s*2+side)*NB+b]=e; } }
int main(int c,char**v){ const char*m=v[1];
 for(int s=0;s<6;s++)for(int r=0;r<2;r++){ const char*q=m+s*7+r*3; if(q[0]=='-'){Nx[s][r]=-1;W[s][r]=1;Mv[s][r]=1;} else {W[s][r]=q[0]-'0';Mv[s][r]=q[1]=='R'?1:-1;Nx[s][r]=q[2]-'A';} }
 double mx=atof(v[2]); char side=v[3][0]; u64 gap=strtoull(v[4],0,10); int dump=atoi(v[5]); double ck=c>6?atof(v[6]):0;
 build();
 long SZ=1L<<26; uint16_t*tp=calloc(SZ,2); long p=SZ/2,lo=p,hi=p; int s=0; int ent=0; // ent: entering from left side(0) => position at leftmost cell
 u64 n=0,last=0; double nextck=ck; 
 for(;;){ if((double)n>=mx)break;
  int ev=0; if(side=='L'&&p<=lo){ if(n-last>=gap)ev=1; last=n; } if(side=='R'&&p>=hi){ if(n-last>=gap)ev=1; last=n; }
  if(p<lo)lo=p; if(p>hi)hi=p;
  if(ev){ printf("EV %llu %c ent%d lo=%ld hi=%ld ",n,'A'+s,ent,lo-SZ/2,hi-SZ/2);
    if(dump){ long a= side=='L'?lo:hi-dump+1; if(a<lo)a=lo; for(long i=a;i<a+dump&&i<=hi;i++){ if(i==p)putchar(ent?'<':'>'); for(int j=K-1;j>=0;j--)putchar('0'+((tp[i]>>j)&1)); } }
    putchar('\n'); fflush(stdout); }
  if(ck&&(double)n>=nextck){ fprintf(stderr,"at %llu lo=%ld hi=%ld\n",n,lo-SZ/2,hi-SZ/2); nextck+=ck; }
  Ent e=T[(s*2+ent)*NB+tp[p]];
  if(e.out==2){ // replay to count exact steps
    int q=ent?K-1:0; unsigned t=tp[p]; int st=s; u64 k=0; for(;;){int r=(t>>(K-1-q))&1; if(Nx[st][r]<0){printf("HALT at step %llu (bbchallenge count), state %c reading %d\n",n+k+1,'A'+st,r);break;} if(W[st][r])t|=1u<<(K-1-q);else t&=~(1u<<(K-1-q)); int mm=Mv[st][r]; st=Nx[st][r]; q+=mm;k++;}
    tp[p]=t; break; }
  if(e.out==3){ printf("LOOP inside block at step %llu\n",n); break; }
  tp[p]=e.nb; s=e.ns; n+=e.st; if(e.out){p++;ent=0;} else {p--;ent=1;}
 }
 printf("END steps=%llu lo=%ld hi=%ld state=%c\n",n,lo-SZ/2,hi-SZ/2,'A'+s);
 if(c>7){ FILE*f=fopen(v[7],"w"); for(long i=lo;i<=hi;i++){ if(i==p)fputc(ent?'<':'>',f); for(int j=K-1;j>=0;j--)fputc('0'+((tp[i]>>j)&1),f);} fputc('\n',f); fclose(f);} }
