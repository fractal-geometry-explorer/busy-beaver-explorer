// The pushdown reduction of py/pds.py, in C (same enumeration, same saturation; tests/test_pds.py checks they agree).
//
// One side of the tape is abstracted by a DFA (read from the far blank end toward the head); the other side is kept
// exactly as a pushdown stack.  Reachability in a pushdown system is regular and computable (post* saturation), so
// for each DFA we compute exactly which abstract configurations are reachable from blank tape and check whether a
// halting transition is among them.  If it is not, the machine never halts (the abstraction over-approximates).
//
// usage: pds N [L|R] [N0]     try every DFA with N0..N states (canonical BFS numbering, delta(0,0)=0) for the left
//                             side (L, default) or the right side (R = run on the mirrored machine); prints
//                             "NONHALT n=..: <delta>" for each DFA that proves non-halting and "n K tried T".
//        TM=<machine> pds ... another 6-state machine in standard text format.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
const char *TEXT="1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LA---_0RC1LA";
int S=6, tw[6][2], td[6][2], ts[6][2], th[6][2];
int n; int d[8][2];
#define MAXV 512
#define WB 8
typedef struct { uint64_t b[WB]; } bs;
bs tr[MAXV][4]; // g: 0,1,2=BOT,3=eps
int mids[64][2][2][2]; // [p2][len-1][x][b] ; len1 uses [p2][0][x][0]
int nv;
int wu[200000], wg[200000], wv[200000], wn;
static inline int has(int u,int g,int v){return (tr[u][g].b[v>>6]>>(v&63))&1;}
static inline void add(int u,int g,int v){ if(has(u,g,v))return; tr[u][g].b[v>>6]|=1ULL<<(v&63); wu[wn]=u;wg[wn]=g;wv[wn]=v;wn++; if(wn>=200000){fprintf(stderr,"overflow\n");exit(1);} }
int predq[8][16], predx[8][16], npred[8];
int epsin[MAXV][64]; int nepsin[MAXV];
int mid(int p2,int len,int x,int b){ int *m=&mids[p2][len-1][x][b]; if(*m<0)*m=nv++; return *m; }
int run(void){
  int P=n*S, FIN=P; nv=P+1;
  memset(tr,0,sizeof(tr)); memset(mids,-1,sizeof(mids)); memset(nepsin,0,sizeof(nepsin)); wn=0;
  memset(npred,0,sizeof(npred));
  for(int q=0;q<n;q++)for(int x=0;x<2;x++){int t=d[q][x]; predq[t][npred[t]]=q; predx[t][npred[t]]=x; npred[t]++;}
  add(0,2,FIN);
  while(wn){ wn--; int u=wu[wn],g=wg[wn],v=wv[wn];
    if(g==3){ if(nepsin[v]<64) epsin[v][nepsin[v]++]=u; else {fprintf(stderr,"eps\n");exit(1);}
      for(int g2=0;g2<3;g2++) for(int w=0;w<nv;w++) if(has(v,g2,w)) add(u,g2,w);
      continue; }
    for(int i=0;i<nepsin[u];i++) add(epsin[u][i],g,v);
    if(u>=P) continue;
    int q=u/S, s=u%S;
    int a = g==2?0:g;
    if(th[s][a]) continue;
    int b=tw[s][a], s2=ts[s][a];
    if(td[s][a]==1){ int p2=d[q][b]*S+s2; if(g==2) add(p2,2,v); else add(p2,3,v); }
    else { for(int k=0;k<npred[q];k++){ int q2=predq[q][k], x=predx[q][k]; int p2=q2*S+s2;
        int m1=mid(p2,1,x,0); add(p2,x,m1);
        if(g==2){ int m2=mid(p2,2,x,b); add(m1,b,m2); add(m2,2,v);} else add(m1,b,v); } }
  }
  for(int q=0;q<n;q++)for(int s=0;s<S;s++)for(int a=0;a<2;a++) if(th[s][a]){ int u=q*S+s;
    for(int w=0;w<nv;w++){ if(has(u,a,w)) return 1; if(a==0&&has(u,2,w)) return 1; } }
  return 0;
}
long cnt;
void rec(int i,int maxs){
  if(i==2*n){ if(maxs==n-1){ cnt++; if(!run()){ printf("NONHALT n=%d:",n); for(int q=0;q<n;q++)printf(" %d%d",d[q][0],d[q][1]); printf("\n"); fflush(stdout);} } return; }
  int q=i/2,x=i%2; if(q>maxs) return;
  for(int v=0; v<n && v<=maxs+1; v++){ if(i==0&&v!=0) continue; d[q][x]=v; rec(i+1, v>maxs?v:maxs); }
}
int main(int argc,char**argv){
  int N=atoi(argv[1]); if(getenv("TM")) TEXT=getenv("TM"); int mir=argc>2&&argv[2][0]=='R'; int n0=argc>3?atoi(argv[3]):1;
  for(int s=0;s<6;s++)for(int a=0;a<2;a++){ const char*t=TEXT+7*s+3*a; if(t[0]=='-'){th[s][a]=1;continue;} tw[s][a]=t[0]-'0'; td[s][a]=(t[1]=='R')?1:-1; if(mir) td[s][a]=-td[s][a]; ts[s][a]=t[2]-'A'; }
  for(n=n0;n<=N;n++){ cnt=0; rec(0,0); printf("n %d tried %ld\n",n,cnt); fflush(stdout);} }
