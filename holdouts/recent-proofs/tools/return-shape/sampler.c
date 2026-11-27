// sampler: run a TM (optionally mirrored), at each "end turn" (head arrives, moving left, on a cell
// strictly left of every 1) print: step, state, and the tape to the right as cells run-lengths of ones
// separated by single zeros (token d = 1^d 0; d=0 token for an extra zero).
// usage: sampler TM mirror(0/1) maxsteps first_n every_k
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<26)
static unsigned char *tape;
int main(int argc,char**argv){
  const char*tm=argv[1]; int mir=atoi(argv[2]); double maxs=atof(argv[3]); long firstn=atol(argv[4]); long every=atol(argv[5]);
  int W[6][2],D[6][2],T[6][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*p=tm+s*7+b*3; if(p[0]=='-'){T[s][b]=-1;W[s][b]=1;D[s][b]=1;continue;}
    W[s][b]=p[0]-'0'; D[s][b]=(p[1]=='R')?1:-1; if(mir)D[s][b]=-D[s][b]; T[s][b]=p[2]-'A';}
  tape=calloc(N,1); long pos=N/2, lo=N/2, hi=N/2-1; // [lo,hi] hull of ones (approx: lo = leftmost 1 exactly maintained)
  int st=0; long long step=0; long turns=0; int inside=0;
  while(step<maxs){
    int b=tape[pos]; int t=T[st][b]; if(t<0){printf("HALT step %lld state %c\n",step,'A'+st);return 0;}
    int w=W[st][b]; tape[pos]=w;
    if(w){ if(pos<lo)lo=pos; if(pos>hi)hi=pos; }
    else { if(pos==lo){ while(lo<=hi && !tape[lo])lo++; } if(pos==hi){ while(hi>=lo && !tape[hi])hi--; } }
    int d=D[st][b]; pos+=d; st=t; step++;
    if(pos<=10||pos>=N-10){fprintf(stderr,"tape overflow\n");break;}
    if(lo>hi) continue;
    if(pos>=lo) inside=1;
    else if(inside && d<0 && pos<lo){ inside=0; turns++;
      if(turns<=firstn || (every>0 && turns%every==0)){
        printf("%lld %c %ld :",step,'A'+st,lo-pos-1);
        long i=lo; while(i<=hi){ long j=i; while(j<=hi&&tape[j])j++; printf(" %ld",j-i); i=j+1; }
        printf("\n");
      }
    }
  }
  fprintf(stderr,"steps %lld turns %ld span %ld\n",step,turns,hi-lo+1);
}
