// One right-end visit of the machine on a word of pairs (X = 01, Y = 11, Z = 10, O = 00, read from the head leftwards),
// with the times and states of the crossings of one cell boundary. Called from py/words.py through ctypes.
#include <stdlib.h>
#include <string.h>
static int W[6][2],Mv[6][2],Nx[6][2];
void setm(const char*m){ for(int s=0;s<6;s++)for(int r=0;r<2;r++){ const char*q=m+s*7+r*3; if(q[0]=='-'){Nx[s][r]=-1;} else {W[s][r]=q[0]-'0';Mv[s][r]=q[1]=='R'?1:-1;Nx[s][r]=q[2]-'A';} } }
// word: chars XYZO, nearest the head first. returns 0 ok, 1 halt, 2 timeout.
// out: new word (buffer cap outcap). info: [0]=steps [1]=minp [2]=halt state [3]=halt pos [4]=steps spent left of bnd [5]=number of crossings
// sig: crossing signature at cell boundary bnd (bnd<0; 0 = none), e.g. "<C>E"
static long long CT[64];
long long* ctimes(){return CT;}
int cvisit(const char*w,long maxsteps,long bnd,char*out,long outcap,long long*info,char*sig,int sigcap){
  long L=strlen(w); long N=2*L+8192; long RM=4096; // cells: index = p + (N-RM) ; p in [-(N-RM), RM)
  char*t=calloc(N,1); long off=N-RM;
  for(long i=0;i<L;i++){ int a=(w[i]=='Y'||w[i]=='Z'), b=(w[i]=='Y'||w[i]=='X'); t[off-1-2*i]=b; t[off-2-2*i]=a; }
  long p=0,minp=0,maxw=-1; int s=0; long long n=0,nl=0; int ns=0,rc=0;
  for(;;){ int r=t[off+p];
    if(Nx[s][r]<0){ info[2]=s; info[3]=p; rc=1; break; }
    t[off+p]=W[s][r]; if(p>maxw)maxw=p; int s2=Nx[s][r]; long p2=p+Mv[s][r];
    if(bnd){ if(p>=bnd&&p2<bnd){ if(ns/2<64)CT[ns/2]=n+1; if(ns+2<sigcap){sig[ns++]='<';sig[ns++]='A'+s2;} } if(p<bnd&&p2>=bnd){ if(ns/2<64)CT[ns/2]=n+1; if(ns+2<sigcap){sig[ns++]='>';sig[ns++]='A'+s2;} } if(p<bnd)nl++; }
    p=p2; s=s2; n++; if(p<minp)minp=p;
    if(p<-off+2||p>=RM-2){ rc=3; break; }
    if(s==0&&p>0&&p>maxw) break;
    if(n>maxsteps){ rc=2; break; } }
  sig[ns]=0; info[0]=n; info[1]=minp; info[4]=nl; info[5]=ns/2;
  if(rc==0){ long hi=p-1; long lo=-off; while(lo<hi&&!t[off+lo])lo++; long k=0;
    for(long i=hi;i>=lo;i-=2){ int b=t[off+i], a=(i-1>=-off)?t[off+i-1]:0; if(k+2>=outcap){rc=4;break;} out[k++]= a?(b?'Y':'Z'):(b?'X':'O'); }
    out[k]=0; }
  free(t); return rc; }
