// Finite-automata-reduction search (any machine, up to 10 DFA states): a DFA d[q][x] on the tape left of the head,
// read from the blank end toward the head (state 0 = blank, d[0][0] = 0), and the least NFA on the head cell and the
// right side that accepts every configuration that can halt (halting transitions, closed under backward steps).
// A DFA works when the start (A on blank tape) is not accepted.  DFAs are enumerated in canonical BFS order; a
// partial DFA whose NFA already accepts the start is pruned (the NFA only grows as entries are filled in).
// build: gcc -O2 -o far far.c     usage: ./far MACHINE NMAX [m]    (m: mirror the machine, DFA on the right side)
// prints "FOUND n=.. d=[[..],..]" or "none"; progress per n on stderr.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint64_t u64;
int S; int tw[8][2], tm[8][2], ts[8][2], th[8][2]; // write, move(+1 R,-1 L), next, halt flag
int n; int d[16][2];
u64 T[2][128];
static inline u64 post(int x, u64 m){ u64 r=0; while(m){ int b=__builtin_ctzll(m); r|=T[x][b]; m&=m-1;} return r; }
long long tried=0;
int check(void){
  int N=n*S, SINK=N;
  for(int x=0;x<2;x++){ for(int u=0;u<=N;u++) T[x][u]=0; T[x][SINK]=1ULL<<SINK; }
  for(int s=0;s<S;s++) for(int x=0;x<2;x++) for(int q=0;q<n;q++){
    int u=q*S+s;
    if(th[s][x]) T[x][u]|=1ULL<<SINK;
    else if(tm[s][x]==1 && d[q][tw[s][x]]>=0) T[x][u]|=1ULL<<(d[q][tw[s][x]]*S+ts[s][x]);
  }
  int changed=1;
  while(changed){ changed=0;
    for(int s=0;s<S;s++) for(int x=0;x<2;x++){ if(th[s][x]||tm[s][x]!=-1) continue;
      int w=tw[s][x], s2=ts[s][x];
      for(int q2=0;q2<n;q2++) for(int y=0;y<2;y++){
        u64 tgt=post(w, T[y][q2*S+s2]);
        if(d[q2][y]<0) continue;
        int u=d[q2][y]*S+s;
        if(tgt & ~T[x][u]){ T[x][u]|=tgt; changed=1; }
      }
    }
    // early exit: if start already reaches sink, fail
  }
  u64 seen=1ULL<<0, fr=seen; // (q0, A)
  while(fr){ u64 nx=post(0,fr)&~seen; seen|=nx; fr=nx; }
  return !((seen>>SINK)&1);
}
// enumerate canonical DFAs: fill slots in BFS order
int slotq[20], slotx[20], nslots;
int found=0;
void rec(int k, int used){
  if(found) return;
  tried++;
  if(!check()) return;
  if(k==nslots){ if(used==n){ if(1){ found=1; printf("FOUND n=%d d=[",n); for(int q=0;q<n;q++) printf("[%d,%d]%s",d[q][0],d[q][1],q<n-1?",":""); printf("]\n"); } } return; }
  int q=slotq[k], x=slotx[k];
  if(q>=used) return; // state q not yet reachable in BFS order -> not canonical
  int lim = used<n ? used+1 : n;
  for(int v=0; v<lim; v++){ d[q][x]=v; rec(k+1, v==used? used+1: used); if(found) return; }
  d[q][x]=-1;
}
int main(int argc,char**argv){
  char *M=strdup(argv[1]); int N=atoi(argv[2]); int mirror=argc>3;
  S=(strlen(M)+1)/7;
  for(int s=0;s<S;s++) for(int x=0;x<2;x++){ char*t=M+7*s+3*x;
    if(t[0]=='-'){ th[s][x]=1; continue; } th[s][x]=0; tw[s][x]=t[0]-'0'; tm[s][x]=(t[1]=='R')?1:-1; if(mirror) tm[s][x]=-tm[s][x]; ts[s][x]=t[2]-'A'; }
  for(n=1;n<=N;n++){
    nslots=0; for(int q=0;q<n;q++) for(int x=0;x<2;x++){ if(q==0&&x==0) continue; slotq[nslots]=q; slotx[nslots]=x; nslots++; }
    for(int q=0;q<16;q++) d[q][0]=d[q][1]=-1; d[0][0]=0; tried=0; rec(0,1);
    if(found) return 0;
    fprintf(stderr,"n=%d tried %lld\n",n,tried); fflush(stderr);
  }
  printf("none\n"); return 0;
}
