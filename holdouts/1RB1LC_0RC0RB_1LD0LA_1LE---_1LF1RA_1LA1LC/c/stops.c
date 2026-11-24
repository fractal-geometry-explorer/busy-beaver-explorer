/* fastdirect.c with a header-prefix test: stop only where state S reads 0, the gap is to the left and the
   cells p..p+nh-1 equal hdr */
#include <stdint.h>
void run(unsigned char *c, long long n, const int *tab, int S, const unsigned char *gap, int ng,
         const unsigned char *hdr, int nh, long long maxn, long long *io){
  long long p=io[0], lo=io[2], hi=io[3], k=0; int s=(int)io[1]; int status=1;
  while(k<maxn){
    if(p<ng+1||p>=n-nh-2){status=3;break;}
    int y=c[p]; const int *t=tab+3*(2*s+y);
    if(t[2]<0){status=2;k++;break;}
    c[p]=(unsigned char)t[0]; p+=t[1]; s=t[2]; k++;
    if(p<lo)lo=p; else if(p>hi)hi=p;
    if(s==S && c[p]==0){
      int ok=1; for(int i=0;i<nh;i++) if(c[p+i]!=hdr[i]){ok=0;break;}
      if(ok) for(int i=0;i<ng;i++) if(c[p-ng+i]!=gap[i]){ok=0;break;}
      if(ok){status=0;break;}
    }
  }
  io[0]=p; io[1]=s; io[2]=lo; io[3]=hi; io[4]=k; io[5]=status;
}
