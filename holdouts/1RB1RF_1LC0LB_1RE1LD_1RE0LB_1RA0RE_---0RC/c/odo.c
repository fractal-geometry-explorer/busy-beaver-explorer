// The run of 1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC from blank tape, with the sweeps over the clean part of the
// block skipped (exactly): see README "The odometer".  Layout once the machine is steady (found at the first steady
// visit): cells left of the seam hold the counter L as 3-cell words x01; the 63 cells from the seam are the window
// (finite control); from cell seam+63 on the block is a row of 4-cell words, 0110 the zero digit, then blank.
//
// Skipped: when the head enters the block from the window in state E, the zero digits in front of the first nonzero
// word are crossed in 4 steps each and are restored when the head comes back over them in state B or D (4 steps
// each); the simulation puts the head on the first nonzero word directly and, when it comes back to the left of that
// word in state B or D, back in the window.  If it comes back in another state the skipped words are written out
// (as 1101) and the run goes on step by step, so the run is exact in every case.
//
// usage: odo MAXSTEPS [plain] [hashevery]
//   prints every change of the state in which the head leaves L (A> or E>), with the window, the block digits and
//   the counters; "plain" switches the skipping off (for comparison); hashevery=K prints a tape hash every K-th
//   crossing of the seam.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define N (1L<<31)
static unsigned char *tp; static long pos, lo_, hi_; static int st; static unsigned long long n;
static const char *TT="1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC";
static int W[6][2],Mv[6][2],Nx[6][2];
static const char *MA[2]={"110110111010011101110111011011101110111011101","110110111011011101110111011011101110111011101"};
static long seam=-1, blk0; static long nwords=0; // block extent in words (non-blank)
static long fnz=0;
static int isz(long i){ long a=blk0+4*i; return tp[a]==0&&tp[a+1]==1&&tp[a+2]==1&&tp[a+3]==0; }
static int wordv(long i){ long a=blk0+4*i; return tp[a]*8+tp[a+1]*4+tp[a+2]*2+tp[a+3]; }
static int match(long p,const char*s){ for(int j=0;s[j];j++) if(tp[p+j]!=s[j]-'0') return 0; return 1; }
static int try_seam(void){ // at a visit: head on blank at hi_
  long e=hi_-1; if(!(tp[e-1]==1&&tp[e]==0)) return 0; e-=1; long m=0; while(match(e-4,"1011")){e-=4;m++;}
  long q=e-15; if(!match(q+1,"01101")||!match(q+7,"01101")||!match(q+13,"01")) return 0;
  q-=45; if(!match(q,MA[0])&&!match(q,MA[1])) return 0;
  if(m<20) return 0;
  seam=q; blk0=seam+63; return 1; }
static uint64_t hash(void){ uint64_t h=1469598103934665603ULL; long a=lo_; while(a<hi_&&tp[a]==0)a++; long b=hi_; while(b>a&&tp[b]==0)b--;
  for(long j=a;j<=b;j++){ h^=tp[j]+1; h*=1099511628211ULL; } h^=(uint64_t)(pos-a)*31+st; h*=1099511628211ULL; return h; }
static void lwords(char*out,int max,long*cnt){ long a=lo_; while(a<seam&&tp[a]==0)a++; long len=seam-a; long pad=(3-len%3)%3; long c=0; int k=0;
  for(long j=a-pad;j<seam;j+=3){ if(k<max) out[k++]='0'+tp[j]; c++; } out[k]=0; *cnt=c; }
int main(int argc,char**argv){
  unsigned long long maxs=strtoull(argv[1],0,10); int plain=argc>2&&!strcmp(argv[2],"plain"); long hashevery=argc>3?atol(argv[3]):0;
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*x=TT+7*s+3*b; if(x[0]=='-'){Nx[s][b]=-1;continue;} W[s][b]=x[0]-'0';Mv[s][b]=x[1]=='R'?1:-1;Nx[s][b]=x[2]-'A';}
  tp=calloc(N,1); if(!tp){fprintf(stderr,"no memory\n");return 1;} pos=N/8; lo_=hi_=pos; st=0; n=0;
  long visits=0; int prevExit=-1; unsigned long long ev=0, evflip=0, sendsE=0, sendsA=0, sendsEflip=0, visflip=0; int afterflip=0;
  long virt=-1; // >=0: words [0,virt) are virtually passed (head is inside the block at word >= virt)
  long lt=1L<<60; // lowest block word touched since last return
  unsigned long long jumps=0, viol=0;
  while(n<maxs){
    if(st==2 && pos==hi_ && tp[pos]==0){ visits++; if(seam<0) { if(try_seam()){ printf("seam found at visit %ld step %llu (cell %ld from the left end)\n",visits,n,seam-lo_);
          nwords=0; while(wordv(nwords)!=0) nwords++; } } }
    int b=tp[pos]; if(Nx[st][b]<0){printf("HALT at step %llu (bbchallenge count %llu)\n",n,n+1);return 0;}
    long q=pos+Mv[st][b]; tp[pos]=W[st][b]; int s2=Nx[st][b];
    if(seam>=0){
      if(pos==seam-1 && q==seam){ ev++;
        if(hashevery && ev%hashevery==0) printf("hash ev %llu step %llu %016llx\n",ev,n+1,(unsigned long long)hash());
        if(prevExit>=0 && s2!=prevExit){
          char lw[200]; long lc; lwords(lw,60,&lc);
          printf("%c>->%c> step %llu visits %ld ev %llu Lwords %ld L=%s G'=",'A'+prevExit,'A'+s2,n+1,visits,ev,lc,lw);
          for(int j=0;j<28;j++)putchar('0'+tp[seam+j]); printf(" t=");
          for(int j=28;j<44;j++){putchar('0'+tp[seam+j]);if(j%4==3)putchar(' ');} printf("I=");
          for(int j=44;j<63;j++)putchar('0'+tp[seam+j]); printf(" blk=");
          long last=0; for(long j=0;j<nwords+2;j++) if(wordv(j)!=6&&wordv(j)!=0) last=j+1;
          for(long j=0;j<last && j<60;j++){ int v=wordv(j); putchar(v==6?'0':v==2?'1':v==14?'2':v==0?'h':'?'); }
          printf(" nonzero-top %ld nwords %ld\n",last,nwords);
          if(prevExit==4&&s2==0){ afterflip=1; evflip=ev; sendsEflip=sendsE; visflip=visits; }
          fflush(stdout);
        }
        prevExit=s2;
      }
      if(pos==blk0-1 && q==blk0){ // entering the block
        if(s2==4) sendsE++; else if(s2==0) sendsA++; else printf("block entered in state %c at step %llu\n",'A'+s2,n+1);
        if(s2==4 && !plain){
          // skip the zero prefix
          while(fnz<nwords && isz(fnz)) fnz++;
          if(fnz>0){ n+=4ULL*fnz; virt=fnz; q=blk0+4*fnz; jumps++; }
          if(fnz>=nwords){ // the send reaches the blank end: a visit happens inside (C on the 4th cell of the last zero word)
            visits++; if(afterflip){ afterflip=0; char lw[200]; long lc; lwords(lw,60,&lc);
              printf("   first visit after E>->A>: bounces %llu sends %llu visit %ld Lwords %ld L=%s\n",ev-evflip+1,sendsE-sendsEflip,visits,lc,lw); fflush(stdout);} }
        }
        if(plain && s2==4 && afterflip){ /* detect all-zero block for the report */ long f=0; while(f<nwords&&isz(f))f++; if(f>=nwords){ afterflip=0; char lw[200]; long lc; lwords(lw,60,&lc);
              printf("   first visit after E>->A>: bounces %llu sends %llu visit %ld Lwords %ld L=%s\n",ev-evflip+1,sendsE-sendsEflip,visits+1,lc,lw);} }
        lt=1L<<60;
      }
      if(q>=blk0){ long wi=(q-blk0)>>2; if(wi<lt) lt=wi; if(wi>=nwords) nwords=wi+1; }
      if(virt>=0 && q==blk0+4*virt-1){ // leaving to the left of the first materialized word
        if(s2==1||s2==3){ n+=4ULL*virt; q=blk0-1; s2=1; virt=-1; }
        else { viol++; printf("skipped prefix entered in state %c at step %llu: writing it out\n",'A'+s2,n+1);
          for(long j=0;j<virt;j++){ long a=blk0+4*j; tp[a]=1;tp[a+1]=1;tp[a+2]=0;tp[a+3]=1; } virt=-1; fnz=0; }
      }
      if(pos==blk0 && q==blk0-1){ virt=-1; }
      if(q==blk0-1 && pos>=blk0){ // back in the window: refresh the first-nonzero pointer
        if(lt<fnz) fnz=lt; while(fnz<nwords && isz(fnz)) fnz++;
        // trim blank words at the end
        while(nwords>0 && wordv(nwords-1)==0 && nwords-1>=fnz+0 && 0) nwords--;
      }
    }
    pos=q; st=s2; n++; if(pos<lo_)lo_=pos; if(pos>hi_)hi_=pos;
    if(pos<=8||pos>=N-8){printf("tape exhausted\n");return 1;}
  }
  printf("end step %llu visits %ld ev %llu sendsE %llu sendsA %llu jumps %llu violations %llu\n",n,visits,ev,sendsE,sendsA,jumps,viol); return 0;
}
