// Accelerated run of 1RB0RE_1LC0RA_0LD0LB_1RE0LB_1RF---_0RB0RC from blank tape.
//
// Whenever A is at the right end of the tape on blank, the tail is checked against the two sweep rules proved in
// lean/Rules.lean:
//   sweep   L 1^4 (10)^(y) 0 1 0 0 (10)^c A>  ->  L (10)^(y+2) 0 1 0 0 (10)^(c+1) A>   (y >= 2, c >= 1, 8y + 4c + 18 steps)
//   sweep_p L 1^2 (10)^y A>                  ->  L (10)^(y+2) A>                     (y >= 1, 4y + 6 steps)
// and if one applies, as many sweeps as the ones allow are done at once (x ones: x/4, resp. x/2 sweeps; the step
// counts are the sums of the proved ones).  Everything else (the events where a segment runs out) is simulated
// step by step, so the run is exact.  No halt is possible inside a batch (each sweep is a proved run).
//
// usage: gcc -O2 -o accel accel.c
//        ./accel MAXSTEPS                    run, print the final step count and tape length
//        ./accel MAXSTEPS x CHK              also print a hash of the tape at the first sweep end at or after CHK
//        ./accel MAXSTEPS plain CHK          the same with single steps only (to compare the two)
//        LOG=1 ./accel MAXSTEPS              log every event (the tape tail as tokens U = 1^k, T = (10)^k, Z = 0^k)
//                                            and every batch (B k)
// It needs 2 GB of memory for the tape (CAP); 1e16 steps take about 10 s.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned long long u64; typedef __uint128_t u128;
#define CAP (1L<<31)
static unsigned char *t;
static void p128(u128 v){char b[50];int i=49;b[i]=0;if(!v){putchar('0');return;}while(v){b[--i]='0'+v%10;v/=10;}fputs(b+i,stdout);}
int main(int argc,char**argv){
  const char*m="1RB0RE_1LC0RA_0LD0LB_1RE0LB_1RF---_0RB0RC";
  double MAX=atof(argv[1]); int plain=argc>2&&!strcmp(argv[2],"plain"); double CHK=argc>3?atof(argv[3]):0;
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){const char*p=m+s*7+r*3; if(p[0]=='-'){ns[s][r]=-1;continue;} nw[s][r]=p[0]-'0';mv[s][r]=p[1]=='R'?1:-1;ns[s][r]=p[2]-'A';}
  t=calloc(CAP,1); long base=1000, pos=base, hi=pos; int st=0; u128 steps=0; long long nb=0,ne=0; u128 batched=0;
  int chkdone=0; int LOG=getenv("LOG")!=0;
  while((double)steps<MAX){
    if(st==0&&pos>=hi&&t[pos]==0){
      if(CHK>0&&!chkdone&&(double)steps>=CHK){chkdone=1; u64 h=1469598103934665603ULL; for(long j=base-500;j<pos;j++){h^=t[j];h*=1099511628211ULL;} printf("CHECK step ");p128(steps);printf(" len %ld hash %llx\n",pos-base,(unsigned long long)h); fflush(stdout); if(plain) return 0;}
      if(!plain){
        long j=pos-1; u64 c=0; while(t[j]==0&&t[j-1]==1){c++;j-=2;}
        if(c>=1&&t[j]==0&&t[j-1]==0&&t[j-2]==1&&t[j-3]==0){
          long j2=j-4; u64 y=0; while(t[j2]==0&&t[j2-1]==1){y++;j2-=2;} u64 x=0; while(t[j2]==1){x++;j2--;}
          if(y>=2&&x>=4){u64 k=x/4; steps+=(u128)k*(8*y+4*c+18)+(u128)10*k*(k-1); batched+=k;
            long w=j2+1; for(u64 i=0;i<x-4*k;i++)t[w++]=1; for(u64 i=0;i<y+2*k;i++){t[w++]=1;t[w++]=0;} t[w++]=0;t[w++]=1;t[w++]=0;t[w++]=0;
            for(u64 i=0;i<c+k;i++){t[w++]=1;t[w++]=0;} pos=w; hi=w; nb++; if(LOG){printf("B %llu\n",(unsigned long long)k);} if(w>CAP-100){printf("cap\n");return 1;} continue;}
        } else if(c>=1&&t[j]==1){ u64 y=c; long j2=j; u64 x=0; while(t[j2]==1){x++;j2--;}
          if(x>=2){u64 k=x/2; steps+=(u128)k*(4*y+6)+(u128)4*k*(k-1); batched+=k;
            long w=j2+1; for(u64 i=0;i<x-2*k;i++)t[w++]=1; for(u64 i=0;i<y+2*k;i++){t[w++]=1;t[w++]=0;} pos=w; hi=w; nb++; if(LOG){printf("B %llu\n",(unsigned long long)k);} if(w>CAP-100){printf("cap\n");return 1;} continue;}
        }
      }
    }
    if(LOG&&st==0&&pos>=hi&&t[pos]==0){
      printf("EV ");p128(steps);printf(" |"); long j=pos-1; int nt=0; char ty[64]; long ln[64];
      while(j>=base&&nt<40){ long k=0; char c;
        if(t[j]==0&&t[j-1]==1){c='T'; while(j>=base&&t[j]==0&&t[j-1]==1){k++;j-=2;}}
        else if(t[j]==1){c='U'; while(j>=base&&t[j]==1){k++;j--;}}
        else {c='Z'; while(j>=base&&t[j]==0&&!(t[j-1]==1&&0)){ if(t[j-1]==1&&k>=1) break; k++; j--; if(t[j]==1) break;}}
        ty[nt]=c; ln[nt]=k; nt++; }
      for(int i=nt-1;i>=0;i--) printf(" %c%ld",ty[i],ln[i]); printf("\n");}
    int r=t[pos]; int q=ns[st][r]; if(q<0){printf("HALT at step ");p128(steps);printf("\n");return 0;}
    t[pos]=nw[st][r]; pos+=mv[st][r]; st=q; steps++; if(pos>hi)hi=pos; if(pos<10){printf("left edge\n");return 1;}
  }
  printf("end: steps ");p128(steps);printf(" len %ld batches %lld sweeps batched ",hi-base,nb);p128(batched);printf("\n");
  return 0;}
