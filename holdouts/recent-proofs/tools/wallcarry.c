// Prints, at each step where the head is within WIN cells of one end (after 1e5 steps), the cells between head and that
// end parsed as segment entries 1^(d+1) followed by 0 or 00 (sep shown as s). Usage: wallcarry MACHINE STEPS SIDE(0=left,1=right) WIN
// When the head is near one end, parse the cells between head and that end as segment entries 1^(d+1) 0|00
// (outward from the head) and print: state headsym nentries d0 d1 ... (with sep bits). side 0 = left end, 1 = right end.
#include <stdio.h>
#include <stdlib.h>
#define T 8000000
static unsigned char tape[T];
int main(int argc,char**argv){
  char *m=argv[1]; long N=atol(argv[2]); int side=atoi(argv[3]); int win=atoi(argv[4]);
  int w[6][2],d[6][2],n[6][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*x=m+7*s+3*b; if(x[0]=='-'){n[s][b]=-1;continue;} w[s][b]=x[0]-'0'; d[s][b]=x[1]=='R'?1:-1; n[s][b]=x[2]-'A';}
  long p=T/2,lo=p,hi=p; int s=0; int dir= side==0?-1:1;
  for(long i=0;i<N;i++){int b=tape[p]; if(n[s][b]<0){printf("HALT %ld\n",i);return 0;} tape[p]=w[s][b]; p+=d[s][b]; s=n[s][b];
    if(p<lo)lo=p; if(p>hi)hi=p; if(p<=2||p>=T-3)break;
    long dist= side==0? p-lo : hi-p;
    if(dist>win) continue;
    if(i<100000) continue;
    // parse outward from p+dir
    long q=p+dir; long end= side==0? lo-1: hi+1; int ne=0; int vals[16]; int seps[16]; int ok=1;
    while(ne<16){
      if((side==0 && q<=end)||(side==1&&q>=end)) break;
      if(tape[q]==0){ // must be blank to the end
        long r=q; int blank=1; while(!((side==0 && r<=end)||(side==1&&r>=end))){ if(tape[r]){blank=0;break;} r+=dir;}
        if(!blank) ok=0; break; }
      int c=0; while(tape[q]==1){c++; q+=dir;}
      int z=0; long r=q; while(z<3 && tape[r]==0 && !((side==0 && r<=end)||(side==1&&r>=end))){z++; r+=dir;}
      if(z==3 || ((side==0 && r<=end)||(side==1&&r>=end))) { vals[ne]=c-1; seps[ne]=0; ne++; // last entry: rest must be blank
        long t=r; int blank=1; while(!((side==0 && t<=end)||(side==1&&t>=end))){ if(tape[t]){blank=0;break;} t+=dir;}
        if(!blank) ok=0; break; }
      vals[ne]=c-1; seps[ne]=(z==2); ne++; q=r;
    }
    if(!ok || ne>6) continue;
    printf("%c%d",'A'+s,b=tape[p]); for(int k=0;k<ne;k++) printf(" %d%s",vals[k],seps[k]?"s":""); printf("\n");
  }
  return 0;
}
