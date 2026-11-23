// psim: simulation of 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD from blank tape, direct except for two
// shortcuts, each a theorem of lean/Pulse.lean (holds for every tape around):
//   right_words A> ws R           -> images(ws) A> R      2 per 01, 5 per 011   (01 -> 11, 011 -> 100)
//   left_words  images(ws) A>111 R-> A>111 ws R           8 per 01, 5 per 011
// (ws = any list of words 01 / 011 in reading order). Shortcuts are used for stretches of at least MINW cells.
// usage: psim MAXSTEPS [LOGFILE|-] [MINW] [SECONDS]   LOGFILE gets "step hash len" at every X visit (C at the left end,
//        tape 0 (011)^a 001101 ...), for comparison with the direct run (MINW 0 turns the
//        shortcuts off: the direct run). Stops after SECONDS of wall clock.
// build: gcc -O2 -o psim psim.c -lm
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>
typedef long long ll;
static unsigned char *t; static unsigned char *buf;
int main(int argc,char**argv){
 const char*mm="1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD"; int W[6][2],D[6][2],N[6][2];
 for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*x=mm+7*s+3*b; if(x[0]=='-'){N[s][b]=-1;continue;} W[s][b]=x[0]-'0';D[s][b]=x[1]=='R'?1:-1;N[s][b]=x[2]-'A';}
 ll MAX=(ll)atof(argv[1]); FILE*lg=argc>2&&strcmp(argv[2],"-")?fopen(argv[2],"w"):0; ll MINW=argc>3?atoll(argv[3]):24; double SECS=argc>4?atof(argv[4]):1e18;
 ll S=1LL<<31; t=calloc(S,1); buf=malloc(S/4); ll p=S/2,lo=p,hi=p; int st=0; ll k=0;
 ll nv=0,np=0,nr=0,nl=0,cp=0,cr=0,cl=0,nX=0; time_t t0=time(0); ll nextrep=1000000;
 for(;;){
  if(k>=MAX) break;
  if(st==0 && MINW>0){ // state A: try shortcuts
   if(t[p]==0&&t[p+1]==1){ // words to the right
     ll q=p,n=0,n2=0; while(t[q]==0&&t[q+1]==1){ if(t[q+2]==1){q+=3;n2++;} else {q+=2;} n++; }
     if(q-p>=MINW){
       ll steps=0;
       // right_words over all n words
       for(ll i=p;i<q;){ if(t[i+2]==1&&i+3<=q){ t[i]=1;t[i+1]=0;t[i+2]=0; i+=3; } else { t[i]=1;t[i+1]=1; i+=2; } }
       steps=2*(n-n2)+5*n2; k+=steps; p=q; if(p>hi)hi=p; nr++; cr+=steps; continue;
     }
   }
   if(t[p]==1&&t[p+1]==1&&t[p+2]==1){ // packet with images to the left
     ll s=p,n=0,n2=0; for(;;){ if(t[s-1]==1&&t[s-2]==1){s-=2;n++;} else if(t[s-1]==0&&t[s-2]==0&&t[s-3]==1){s-=3;n++;n2++;} else break; }
     if(p-s>=MINW){
       // images [s,p) -> words, packet moves to s: result 111 at [s,s+3), words at [s+3,p+3)
       ll c=0; for(ll i=s;i<p;){ if(t[i]==1&&t[i+1]==1){ buf[c++]=0;buf[c++]=1;i+=2;} else { buf[c++]=0;buf[c++]=1;buf[c++]=1;i+=3;} }
       t[s]=1;t[s+1]=1;t[s+2]=1; memcpy(t+s+3,buf,c);
       ll steps=8*(n-n2)+5*n2; k+=steps; p=s; if(p<lo)lo=p; nl++; cl+=steps; continue;
     }
   }
  }
  int b=t[p]; int ns=N[st][b]; k++; if(ns<0){printf("HALT at step %lld\n",k);fflush(stdout);return 0;}
  t[p]=W[st][b]; p+=D[st][b]; st=ns; if(p<lo)lo=p; if(p>hi)hi=p;
  if(p<64||p>S-64){fprintf(stderr,"tape full\n");return 1;}
  if(st==2&&p==lo){
    ll q=lo+1; while(q+2<=hi&&t[q]==0&&t[q+1]==1&&t[q+2]==1)q+=3;
    if(q+5<=hi&&t[q]==0&&t[q+1]==0&&t[q+2]==1&&t[q+3]==1&&t[q+4]==0&&t[q+5]==1){ nX++;
      if(lg){ uint64_t h=1469598103934665603ULL; for(ll j=lo;j<=hi;j++) h=(h^t[j])*1099511628211ULL; fprintf(lg,"%lld %llx %lld\n",k,(unsigned long long)h,hi-lo); } }
    if((++nv&255)==0 || k>=nextrep){ if(difftime(time(0),t0)>SECS) break; }
    if(k>=nextrep){ fprintf(stderr,"%ld s step %lld (10^%.2f) len %lld X %lld right %lld (%lld steps) left %lld (%lld steps)\n",(long)(time(0)-t0),k,log10((double)k),hi-lo,nX,nr,cr,nl,cl); nextrep=k*2; }
  }
 }
 printf("no halt in %lld steps; len %lld; X %lld; right sweeps %lld (%lld steps), left %lld (%lld steps); %ld s\n",k,hi-lo,nX,nr,cr,nl,cl,(long)(time(0)-t0)); return 0;}
