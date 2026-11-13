// tapehash M N
//
// Hashes of the run from blank tape, for finding related machines among many (holdouts/related.py):
//
//   L step hash          the tape and the head position (absolute) at steps 10^3, 3*10^3, ..., 3*10^5 and N.
//                        Two machines with equal lines have, with overwhelming probability, the same tape and head
//                        at those steps; tools/c/lockstep.c then compares the pair step by step.
//   R step hash mirror   the tape around the head, whatever the state and up to a shift, at each of the first 3000
//                        moments the head reaches a new cell once 30 cells are visited; `mirror` is the hash of
//                        the reflected tape. Two machines with many equal R hashes go through the same tapes,
//                        possibly at different steps; tools/c/cfgmatch.c (blind) then counts all of them.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128; typedef uint64_t u64;
#define P ((1ULL<<61)-1)
#define X 1000003ULL
static u64 mm(u64 a,u64 b){u128 t=(u128)a*b; u64 r=(u64)(t&P)+(u64)(t>>61); if(r>=P)r-=P; return r;}
static u64 pw(u64 a,u64 e){u64 r=1; while(e){if(e&1)r=mm(r,a); a=mm(a,a); e>>=1;} return r;}
typedef struct{int w,d,n;} tr;
int main(int c,char**v){ if(c<3){fprintf(stderr,"usage: tapehash M N\n");return 2;}
  const char*m=v[1]; long N=atol(v[2]); tr T[6][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*t=m+7*s+3*b; if(t[0]=='-'){T[s][b].n=-1;} else {T[s][b].w=t[0]-'0';T[s][b].d=t[1]=='R'?1:-1;T[s][b].n=t[2]-'A';}}
  u64 XI=pw(X,P-2); long W=2*N+10; unsigned char*tape=calloc(W,1); long h=N+5,h0=h,lo=h,hi=h,nrec=0; int s=0; u64 H=0,pf=1,T0=0,T1=0;
  for(long t=0;t<=N;t++){
    if(t==1000||t==3000||t==10000||t==30000||t==100000||t==300000||t==N)
      printf("L %ld %llu\n",t,(unsigned long long)(H^((u64)(h-h0)*0x9E3779B97F4A7C15ULL)));
    if(h<lo||h>hi){ if(h<lo)lo=h; else hi=h; if(hi-lo>=30&&nrec<3000){ printf("R %ld %llu %llu\n",t,(unsigned long long)T0,(unsigned long long)T1); nrec++; } }
    if(t==N)break;
    int b=tape[h]; tr x=T[s][b]; if(x.n<0)break;
    if(x.w!=b){ H=x.w?(H+pf)%P:(H+P-pf)%P; T0=x.w?(T0+1)%P:(T0+P-1)%P; T1=x.w?(T1+1)%P:(T1+P-1)%P; tape[h]=x.w; }
    if(x.d>0){ pf=mm(pf,X); T0=mm(T0,XI); T1=mm(T1,X); h++; } else { pf=mm(pf,XI); T0=mm(T0,X); T1=mm(T1,XI); h--; }
    s=x.n; }
  return 0; }
