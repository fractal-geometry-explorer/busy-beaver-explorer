// Invariant search with the word unknown: every left DFA (reading from the far left to the head) with up to NMAX
// states, enumerated depth first with transitions added only when needed; for each, the least right NFA (head cell
// included) that makes the set of configurations closed under steps is computed (finite-automata reduction, "FAR
// direct").  The start is 0^inf STATE> PREFIX W for EVERY word W (the right NFA reaches a state accepting {0,1}*).
// A DFA is rejected as soon as a halting transition becomes possible; a complete DFA that survives is an invariant.
// NMIN in the environment starts at that size.
// usage: farsearch MACHINE NMAX STARTSTATE PREFIX        e.g. farsearch 1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB 8 E 11110
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MAXS 1024
#define W64 16
typedef struct { uint64_t w[W64]; } bs;
static int NW;
static inline void bset(bs*a,int i){a->w[i>>6]|=1ULL<<(i&63);}
static inline int bget(const bs*a,int i){return (a->w[i>>6]>>(i&63))&1;}
static inline int bor(bs*a,const bs*b){int ch=0;for(int i=0;i<NW;i++){uint64_t x=a->w[i]|b->w[i];if(x!=a->w[i]){a->w[i]=x;ch=1;}}return ch;}
static inline int bany(const bs*a,const bs*b){for(int i=0;i<NW;i++)if(a->w[i]&b->w[i])return 1;return 0;}
int tw[6][2],td[6][2],tt[6][2],th[6][2]; // write, dir(+1/-1), next, halting
int n; int delta[64][2]; // -1 undefined
int q0s; int pre[64],npre;
int NS; int nL; int leftrule[12][2]; // (f,b) of left-moving
#define Nst(q,f) ((q)*6+(f))
#define Bst(q,f,b) (6*n+((q)*6+(f))*2+(b))
#define Ast(p,c,r) (18*n+(((p)*2+(c))*nL+(r)))
int Sbase,U,Z;
bs eps[MAXS],e[2][MAXS],acc,cl[MAXS],prod;
long nodes=0;
int solve(void){
  int AS=18*n+n*2*nL; Sbase=AS; U=Sbase+npre+1; Z=U+1; NS=Z+1;
  NW=(NS+63)/64; if(NS>MAXS){fprintf(stderr,"too many\n");exit(1);}
  memset(eps,0,sizeof(bs)*NS);memset(e,0,sizeof(bs)*2*MAXS);memset(&acc,0,sizeof acc);
  bset(&acc,U);bset(&acc,Z);bset(&e[0][U],U);bset(&e[1][U],U);bset(&e[0][Z],Z);
  bset(&eps[Nst(0,q0s)],Sbase);
  for(int i=0;i<npre;i++) bset(&e[pre[i]][Sbase+i],Sbase+i+1);
  bset(&eps[Sbase+npre],U);
  for(int f=0;f<6;f++)for(int b=0;b<2;b++){ if(th[f][b])continue; int w=tw[f][b],t=tt[f][b];
    if(td[f][b]<0){ int r=-1; for(int k=0;k<nL;k++)if(leftrule[k][0]==f&&leftrule[k][1]==b)r=k;
      for(int p=0;p<n;p++)for(int c=0;c<2;c++){int q=delta[p][c]; if(q<0)continue;
        int a=Ast(p,c,r); bset(&e[c][Nst(p,t)],a); bset(&e[w][a],Bst(q,f,b)); }
    } else { for(int q=0;q<n;q++){int q2=delta[q][w]; if(q2<0)continue; bset(&eps[Nst(q2,t)],Bst(q,f,b));} }
  }
  for(;;){
    // closures
    for(int x=0;x<NS;x++){memset(&cl[x],0,sizeof(bs));bset(&cl[x],x);}
    int ch=1; while(ch){ch=0; for(int x=0;x<NS;x++){ for(int i=0;i<NW;i++){uint64_t m=eps[x].w[i]; while(m){int y=i*64+__builtin_ctzll(m); m&=m-1; if(bor(&cl[x],&cl[y]))ch=1;}}}}
    int changed=0;
    for(int q=0;q<n;q++)for(int f=0;f<6;f++)for(int b=0;b<2;b++){
      int B=Bst(q,f,b), N=Nst(q,f); bs tg; memset(&tg,0,sizeof tg);
      for(int i=0;i<NW;i++){uint64_t m=cl[N].w[i]; while(m){int y=i*64+__builtin_ctzll(m); m&=m-1; bor(&tg,&e[b][y]);}}
      if(bor(&eps[B],&tg))changed=1;
      if(b==0 && bany(&cl[N],&acc) && !bget(&acc,B)){bset(&acc,B);changed=1;}
    }
    if(!changed)break;
  }
  // productive
  prod=acc; int ch=1;
  while(ch){ch=0; for(int x=0;x<NS;x++){ if(bget(&prod,x))continue; if(bany(&eps[x],&prod)||bany(&e[0][x],&prod)||bany(&e[1][x],&prod)){bset(&prod,x);ch=1;}}}
  for(int q=0;q<n;q++)for(int f=0;f<6;f++)for(int b=0;b<2;b++){ if(!th[f][b])continue; int N=Nst(q,f);
    if(b==0 && bany(&cl[N],&acc)) return 0;
    for(int i=0;i<NW;i++){uint64_t m=cl[N].w[i]; while(m){int y=i*64+__builtin_ctzll(m); m&=m-1; if(bany(&e[b][y],&prod))return 0;}}
  }
  return 1;
}
int rec(int used){
  nodes++;
  if(!solve())return 0;
  // reachable, first undefined
  int R[64]={0},st[64],sp=0; R[0]=1;st[sp++]=0;
  while(sp){int q=st[--sp]; for(int c=0;c<2;c++){int r=delta[q][c]; if(r>=0&&!R[r]){R[r]=1;st[sp++]=r;}}}
  for(int q=0;q<n;q++) if(R[q]) for(int c=0;c<2;c++) if(delta[q][c]<0){
    int lim=used+1<n?used+1:n;
    for(int r=0;r<lim;r++){ delta[q][c]=r; if(rec(used>r+1?used:r+1))return 1; }
    delta[q][c]=-1; return 0;
  }
  return 1;
}
int main(int argc,char**argv){
  char*m=argv[1]; int nmax=atoi(argv[2]); q0s=argv[3][0]-'A';
  npre=0; for(char*p=argv[4];*p;p++) if(*p=='0'||*p=='1') pre[npre++]=*p-'0';
  int mirror=argc>5;
  nL=0;
  for(int f=0;f<6;f++)for(int b=0;b<2;b++){char*s=m+7*f+3*b; if(s[0]=='-'||s[0]=='H'){th[f][b]=1;continue;} th[f][b]=0;
    tw[f][b]=s[0]-'0'; td[f][b]=(s[1]=='R')?1:-1; if(mirror)td[f][b]=-td[f][b]; tt[f][b]=s[2]-'A'; }
  for(int f=0;f<6;f++)for(int b=0;b<2;b++) if(!th[f][b]&&td[f][b]<0){leftrule[nL][0]=f;leftrule[nL][1]=b;nL++;}
  int nmin=getenv("NMIN")?atoi(getenv("NMIN")):1; for(n=nmin;n<=nmax;n++){
    for(int i=0;i<64;i++)delta[i][0]=delta[i][1]=-1; delta[0][0]=0; nodes=0;
    int r=rec(1);
    printf("n=%d %s nodes=%ld\n",n,r?"FOUND":"none",nodes);
    if(r){ for(int q=0;q<n;q++)printf(" %d:%d,%d",q,delta[q][0],delta[q][1]); printf("\n"); return 0;}
    fflush(stdout);
  }
  return 1;
}
