// lock2 H P T [K]: two machines on (what should stay) one tape, from blank.  In sync = same tape and head; the states
// may differ.  While both would write the same symbol and move the same way they step together.  Otherwise (a break)
// the smallest n+m (1<=n,m<=K) is searched such that H after n steps and P after m steps have the same tape and head
// again; the probe steps are undone and exactly n and m steps are made.  Stops at: T steps of H, a halt, or a break
// with no re-sync within K.  Tapes are compared by a 61-bit polynomial hash of the cells (position-weighted).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned __int128 u128; typedef uint64_t u64;
#define PR ((1ULL<<61)-1)
static inline u64 mm(u64 a,u64 b){u128 t=(u128)a*b; u64 lo=(u64)(t&PR), hi=(u64)(t>>61); u64 s=lo+hi; if(s>=PR)s-=PR; return s;}
static u64 pw(u64 a,u64 e){u64 r=1; while(e){if(e&1)r=mm(r,a); a=mm(a,a); e>>=1;} return r;}
#define TL (1u<<29)
#define KMAX 256
typedef struct { int w[12],mv[12],ns[12]; uint8_t*tape; long pos; int s; u64 h,rp; u64 steps; int halted; } M;
typedef struct { long pos; uint8_t old; u64 h,rp; int s; } U;
static u64 R,RI;
static void parse(M*m,const char*t0){ for(int i=0;i<6;i++)for(int b=0;b<2;b++){const char*t=t0+i*7+b*3;int k=i*2+b;
    if(t[0]=='-'){m->ns[k]=-1;m->w[k]=0;m->mv[k]=0;} else {m->w[k]=t[0]-'0';m->mv[k]=t[1]=='R'?1:-1;m->ns[k]=t[2]-'A';}}
  m->tape=calloc(TL,1); m->pos=TL/2; m->s=0; m->h=0; m->rp=1; m->steps=0; m->halted=0; }
static inline void step(M*m,U*u){ int k=m->s*2+m->tape[m->pos]; if(m->ns[k]<0){m->halted=1;return;}
  if(u){u->pos=m->pos;u->old=m->tape[m->pos];u->h=m->h;u->rp=m->rp;u->s=m->s;}
  if(m->w[k]!=m->tape[m->pos]){ if(m->w[k]){m->h+=m->rp; if(m->h>=PR)m->h-=PR;} else {m->h+=PR-m->rp; if(m->h>=PR)m->h-=PR;} m->tape[m->pos]=m->w[k]; }
  if(m->mv[k]>0){m->pos++; m->rp=mm(m->rp,R);} else {m->pos--; m->rp=mm(m->rp,RI);} m->s=m->ns[k]; m->steps++; }
static void undo(M*m,U*u){ m->tape[u->pos]=u->old; m->pos=u->pos; m->h=u->h; m->rp=u->rp; m->s=u->s; m->steps--; m->halted=0; }
int main(int argc,char**argv){
  R=0x1234567890abcdefULL%PR; RI=pw(R,PR-2); M H,P; parse(&H,argv[1]); parse(&P,argv[2]); u64 T=(u64)atof(argv[3]); int K=argc>4?atoi(argv[4]):60;
  u64 nb=0,lastb=0; static u64 kinds[64][6]; int nk=0;
  while(H.steps<T){
    int k=H.s*2+H.tape[H.pos], q=P.s*2+P.tape[P.pos];
    if(H.ns[k]<0&&P.ns[q]<0){ printf("BOTH HALT in sync: H step %llu, P step %llu, breaks %llu\n",(unsigned long long)H.steps,(unsigned long long)P.steps,(unsigned long long)nb); goto done; }
    if(H.ns[k]>=0&&P.ns[q]>=0&&H.w[k]==P.w[q]&&H.mv[k]==P.mv[q]){ step(&H,0); step(&P,0); continue; }
    // break
    static U uh[KMAX],up[KMAX]; u64 hh[KMAX+1][2],ph[KMAX+1][2]; int hn=0,pn=0;
    hh[0][0]=H.h;hh[0][1]=H.pos; ph[0][0]=P.h;ph[0][1]=P.pos;
    while(hn<K){ step(&H,&uh[hn]); if(H.halted)break; hn++; hh[hn][0]=H.h; hh[hn][1]=H.pos; }
    while(pn<K){ step(&P,&up[pn]); if(P.halted)break; pn++; ph[pn][0]=P.h; ph[pn][1]=P.pos; }
    int hhalt=H.halted, phalt=P.halted, fn=-1,fm=-1;
    for(int s=2;s<=hn+pn&&fn<0;s++) for(int n=1;n<=hn&&n<s;n++){ int m=s-n; if(m>pn)continue; if(hh[n][0]==ph[m][0]&&hh[n][1]==ph[m][1]){fn=n;fm=m;break;} }
    H.halted=0;P.halted=0;
    if(fn<0){ for(int i=hn-1;i>=0;i--)undo(&H,&uh[i]); for(int i=pn-1;i>=0;i--)undo(&P,&up[i]);
      printf("NO RE-SYNC at break %llu: H step %llu in %c reading %d, P step %llu in %c; within %d steps H halts: %s (after %d), P halts: %s (after %d)\n",(unsigned long long)nb+1,(unsigned long long)H.steps,'A'+k/2,k%2,(unsigned long long)P.steps,'A'+q/2,K,hhalt?"yes":"no",hn,phalt?"yes":"no",pn); goto done; }
    for(int i=hn-1;i>=fn;i--)undo(&H,&uh[i]); for(int i=pn-1;i>=fm;i--)undo(&P,&up[i]);
    nb++; lastb=H.steps-fn;
    { int f=0; for(int i=0;i<nk;i++) if(kinds[i][0]==(u64)k&&kinds[i][1]==(u64)q&&kinds[i][2]==(u64)fn&&kinds[i][3]==(u64)fm){kinds[i][4]++;kinds[i][5]=lastb;f=1;break;}
      if(!f&&nk<64){kinds[nk][0]=k;kinds[nk][1]=q;kinds[nk][2]=fn;kinds[nk][3]=fm;kinds[nk][4]=1;kinds[nk][5]=lastb;nk++;} }
  }
  printf("IN SYNC through H step %llu (P step %llu)\n",(unsigned long long)H.steps,(unsigned long long)P.steps);
done:
  printf("breaks %llu, last at H step %llu\n",(unsigned long long)nb,(unsigned long long)lastb);
  for(int i=0;i<nk;i++) printf("  H in %c%d, P in %c%d: re-sync after %llu and %llu steps, %llu times, last at H step %llu\n",'A'+(int)kinds[i][0]/2,(int)kinds[i][0]%2,'A'+(int)kinds[i][1]/2,(int)kinds[i][1]%2,(unsigned long long)kinds[i][2],(unsigned long long)kinds[i][3],(unsigned long long)kinds[i][4],(unsigned long long)kinds[i][5]);
}
