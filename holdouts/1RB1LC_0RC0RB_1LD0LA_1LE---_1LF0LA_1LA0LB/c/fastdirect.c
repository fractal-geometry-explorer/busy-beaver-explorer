/* direct simulation on a byte buffer, for accel2.py via ctypes.
   tab[3*(2*s+y)] = (w, d, ns) with ns=-1 halt.  Runs until the head is in state S on a 0 with the cells just left
   of it equal to gap[0..ng-1] and the cell right of it equal to r1 (r1<0: any) (after >=1 step), or maxn steps,
   or a halt, or the head reaches the buffer margin.  io: 0 pos, 1 state, 2 lo, 3 hi, 4 steps done, 5 status
   (0 stop, 1 maxn, 2 halt, 3 margin). */
#include <stdint.h>
void run(unsigned char *c, long long n, const int *tab, int S, const unsigned char *gap, int ng, int r1,
         long long maxn, long long *io){
  long long p=io[0], lo=io[2], hi=io[3], k=0; int s=(int)io[1]; int status=1;
  while(k<maxn){
    if(p<ng+1||p>=n-2){status=3;break;}
    int y=c[p]; const int *t=tab+3*(2*s+y);
    if(t[2]<0){status=2;k++;break;}
    c[p]=(unsigned char)t[0]; p+=t[1]; s=t[2]; k++;
    if(p<lo)lo=p; else if(p>hi)hi=p;
    if(s==S && c[p]==0 && (r1<0 || c[p+1]==r1)){
      int ok=1; for(int i=0;i<ng;i++) if(c[p-ng+i]!=gap[i]){ok=0;break;}
      if(ok){status=0;break;}
    }
  }
  io[0]=p; io[1]=s; io[2]=lo; io[3]=hi; io[4]=k; io[5]=status;
}
