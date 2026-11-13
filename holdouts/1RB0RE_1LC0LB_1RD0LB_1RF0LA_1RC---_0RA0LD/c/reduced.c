// reduced engine simulator: real TM, but at each round-trip event the U-stack is refilled to K units (of 20 cells)
// and the V block is cut back to M0 copies. Prints per round trip: rt, real-equivalent? no; consumption, P tokens.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int W[8][2],D[8][2],S[8][2];
#define SZ (1<<20)
unsigned char c[SZ], nb[SZ];
char tk[SZ]; int tp[SZ]; int nt;
int tokenize(int lo,int hi){ // tokens of cells lo..hi-1
  nt=0; int i=lo;
  while(i<hi){
    if(c[i]==0){tk[nt]='_';tp[nt++]=i;i++;continue;}
    int r=0; while(i+r<hi&&c[i+r])r++;
    if(i+r>=hi) break;
    tk[nt]= r==1?'a':r==2?'c':r==3?'b':'X'; tp[nt++]=i; i+=r+1;
  }
  tk[nt]=0; tp[nt]=i; return nt;
}
int main(int argc,char**argv){
 const char*m="1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD";
 long long RT=atoll(argv[1]); int K=atoi(argv[2]), M0=atoi(argv[3]); int verbose=argc>4?atoi(argv[4]):1;
 long long WARM=argc>5?atoll(argv[5]):300000000LL; long long DUMP=argc>6?atoll(argv[6]):-1;  // real steps before starting reduction
 for(int s=0;s<6;s++)for(int y=0;y<2;y++){const char*t=m+7*s+3*y; if(t[2]=='-'){S[s][y]=-1;continue;} W[s][y]=t[0]-'0';D[s][y]=t[1]=='R'?1:-1;S[s][y]=t[2]-'A';}
 int p=SZ/2,lo=p,hi=p,st=0,flag=0; long long k=0,rt=0; int lastK=-1;
 const char*Ub="10101010101010101110"; const char*Vb="1011101110";
 while(rt<RT){
  int y=c[p],s2=S[st][y]; if(s2<0){printf("HALT rt %lld step %lld\n",rt,k);return 0;}
  c[p]=W[st][y];p+=D[st][y];st=s2;k++;
  if(p<lo)lo=p; if(p>hi){hi=p;flag=1;}
  if(p<5||p>SZ-5){printf("OUT\n");return 1;}
  if(flag && p==hi-60){ flag=0;
    if(k<WARM) continue;
    tokenize(lo,p-20);
    // find U run
    int s=-1; for(int i=0;i+27<=nt;i++) if(!strncmp(tk+i,"aaaaaaaabaaaaaaaabaaaaaaaab",27)){s=i;break;}
    if(s<0){ if(verbose)printf("NOSTACK rt %lld\n",rt); rt++; continue;}
    int e=s,nU=0; while(!strncmp(tk+e,"aaaaaaaab",9)){e+=9;nU++;}
    // junction aa then abb*
    if(strncmp(tk+e,"aa",2)){ printf("NOJUNC rt %lld: %.40s\n",rt,tk+e); return 1;}
    int f=e+2, mV=0; while(f+3<=nt && !strncmp(tk+f,"abb",3)){f+=3;mV++;}
    rt++;
    int cons = lastK>=0 ? lastK-nU : 0;
    if(verbose){ printf("%lld %lld %d %d %.*s\n",rt,k,cons,mV,s,tk); }
    // rebuild
    int ustart=tp[s], uend=tp[e]; int vcut0=tp[e+2], vcut1=tp[e+2+3*(mV>M0?mV-M0:0)];
    int n=0; int us0=ustart-lo;
    for(int i=lo;i<ustart;i++) nb[n++]=c[i];
    for(int u=0;u<K;u++) for(int j=0;j<20;j++) nb[n++]=Ub[j]-'0';
    for(int i=uend;i<vcut0;i++) nb[n++]=c[i];
    int newp=-1,newhi=-1;
    for(int i=vcut1;i<=hi+2;i++){ if(i==p)newp=n; if(i==hi)newhi=n; nb[n++]=c[i]; }
    memset(c,0,SZ); int base=SZ/2-n/2; memcpy(c+base,nb,n); lo=base; p=base+newp; hi=base+newhi;
    lastK=K;
    if(rt==DUMP){ int ns=base+us0; printf("DUMP %d %d %d %d %d ",st,p-lo,ns-lo,ns-lo+20*K, ns-lo+20*K+(vcut0-uend)); for(int i=lo;i<=hi+2;i++)putchar('0'+c[i]); printf("\n"); return 0;}
  }
 }
}
