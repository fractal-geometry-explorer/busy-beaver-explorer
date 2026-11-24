// One sweep of 1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA for py/phasemap.py (loaded with ctypes; the Python fallback does the same).
// The head starts in C on cell p (a 0 at the right end); it runs until C next reads a 0 at the right end.
#include <string.h>
// raw sweep: tape buffer t (size cap), content already placed; returns steps or -1 halt, -2 left escape, -3 overflow
// p: head index, hi: initial hi. outputs lo, hi
static const int W[12]={1,0,1,1,0,0,1,1,1,-9,0,1};
static const int Mv[12]={1,-1,1,1,1,1,-1,-1,-1,0,-1,-1};
static const int Nx[12]={1,5,2,1,3,2,4,5,3,-1,1,0};
long sweep(unsigned char*t,long cap,long p,long lo0,long*plo,long*phi,long*hstep){
  long hi=p,lo=lo0,i=0;int s=2;
  for(;;){int r=t[p];
    if(i>0&&s==2&&r==0&&p>=hi)break;
    int e=s*2+r; if(e==9){*hstep=i;return -1;}
    t[p]=W[e];p+=Mv[e];s=Nx[e];i++;
    if(p<lo){lo=p; if(p<0) return -2;}
    if(p>hi){hi=p; if(p>=cap-1) return -3;}
  }
  *plo=lo;*phi=hi;return i;
}
