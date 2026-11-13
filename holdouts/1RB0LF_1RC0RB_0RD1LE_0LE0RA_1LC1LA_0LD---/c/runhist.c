// runhist MACHINE STEPS [SAMPLE]: at every SAMPLE-th left/right record, histogram of interior run lengths
// (excluding the outermost run at each end and the runs at and next to the head), for L- and R-events separately.
#include "../../../tools/c/tm.h"
#define CAP 200000
long long h[2][2][CAP+1]; long long ev[2];
static int len[4000000]; static char sym[4000000]; static char hh[4000000];
int main(int argc,char**argv){tm_machine m; tm_parse(argv[1],&m); long long N=atoll(argv[2]); long long S=argc>3?atoll(argv[3]):1;
 tm_tape t; tm_tape_init(&t,1<<20); int st=0; long long k=0, rec[2]={0,0};
 while(k<N){ long long lo=t.lo,hi=t.hi; k++; if(!tm_step(&m,&t,&st)){printf("halted %lld\n",k);break;}
  int side=-1; if(t.lo<lo) side=0; else if(t.hi>hi) side=1; if(side<0) continue;
  if((rec[side]++)%S) continue; ev[side]++;
  long long p=t.lo; int nr=0;
  while(p<=t.hi){ int v=tm_get(&t,p); long long q=p; int x=0; while(q<=t.hi && tm_get(&t,q)==v){ if(q==t.head) x=1; q++;} if(nr<4000000){len[nr]=q-p; sym[nr]=v; hh[nr]=x; nr++;} p=q; }
  for(int i=1;i<nr-1;i++){ if(hh[i]||hh[i-1]||hh[i+1]) continue; int L=len[i]>CAP?CAP:len[i]; h[side][(int)sym[i]][L]++; }
 }
 for(int s=0;s<2;s++){ printf("%s-events %lld\n", s?"R":"L", ev[s]);
   for(int y=1;y>=0;y--){ printf("  %d-runs:",y); for(int L=1;L<=CAP;L++) if(h[s][y][L]) printf(" %d:%lld",L,h[s][y][L]); printf("\n"); } }
}
