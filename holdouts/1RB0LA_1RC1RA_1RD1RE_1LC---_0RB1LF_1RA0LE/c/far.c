/* far.c: a finite-automata-reduction (co-CTL) search, shared by the G11 batch-4 folders.
 *
 *   gcc -O2 -o far far.c && ./far MACHINE NMAX [m]        (m: the mirror image, DFA on the right part)
 *
 * For every DFA with n <= NMAX states (canonical numbering, d(0,0) = 0) reading the tape left of the head, it computes
 * the least NFA on (TM state x DFA state) + {bottom} that accepts every halting configuration and every predecessor of
 * an accepted one: a right move (f,r)->(w,R,t) needs the edge (f,q) -r-> (t,d(q,w)); a left move (f,r)->(w,L,t) needs
 * (f,d(q,b)) -r-> every state that (t,q) reaches on b then w; a halting (f,r) needs (f,q) -r-> bottom, which loops.
 * If the start  0^k A 0^k  is then not accepted, the accepted language is a co-CTL and the machine never halts; the
 * DFA is printed (FOUND).  Prints the number of DFAs tried at each n.  No result is trusted without a Lean check.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned __int128 u128;
int W[6][2],MV[6][2],NX[6][2]; int NQ=6;
int n; int del[16][2];
long long tried=0;
#define MAXN 16
static u128 T[2][6*MAXN+1];
static int bot;
static inline int id(int f,int q){return f*n+q;}
u128 img(u128 X,int b){u128 r=0; for(int s=0;s<=bot;s++) if((X>>s)&1) r|=T[b][s]; return r;}
int check(){
  bot=NQ*n; memset(T,0,sizeof T);
  T[0][bot]=T[1][bot]=(u128)1<<bot;
  for(int f=0;f<NQ;f++)for(int r=0;r<2;r++){
    if(NX[f][r]<0){ for(int q=0;q<n;q++) T[r][id(f,q)]|=(u128)1<<bot; continue;}
    if(MV[f][r]==1){int w=W[f][r],t=NX[f][r]; for(int q=0;q<n;q++) T[r][id(f,q)]|=(u128)1<<id(t,del[q][w]);}
  }
  int ch=1;
  while(ch){ch=0;
    for(int f=0;f<NQ;f++)for(int r=0;r<2;r++){ if(NX[f][r]<0||MV[f][r]==1)continue;
      int w=W[f][r],t=NX[f][r];
      for(int q=0;q<n;q++)for(int b=0;b<2;b++){
        u128 X=img(img((u128)1<<id(t,q),b),w);
        u128 *dst=&T[r][id(f,del[q][b])];
        if((X & ~*dst)){*dst|=X; ch=1;}
      }
    }
    { u128 all=img((u128)1<<id(0,0),0); while(1){ if((all>>bot)&1) return 0; u128 Y=img(all,0)|all; if(Y==all)break; all=Y;} }
  }
  u128 X=img((u128)1<<id(0,0),0), all=X;
  while(1){ if((all>>bot)&1) return 0; u128 Y=img(all,0)|all; if(Y==all)break; all=Y;}
  return 1;
}
// enumerate canonical DFAs: del[q][b], states numbered by first appearance in order (0,0),(0,1),(1,0),...
int found=0;
void printsol(){
  printf("FOUND n=%d dfa:",n); for(int q=0;q<n;q++) printf(" %d%d",del[q][0],del[q][1]); printf("\n");
  fflush(stdout);
}
void rec(int pos,int used){
  if(found) return;
  if(pos==2*n){ if(used<n) return; tried++; if(check()){found=1;printsol();} return;}
  int q=pos/2,b=pos%2;
  if(q>=used) return; // unreachable state
  int lim = used<n? used+1: n;
  for(int v=0; v<lim; v++){
    if(pos==0 && v!=0) continue; // del[0][0]=0
    del[q][b]=v; rec(pos+1, v==used? used+1: used);
    if(found) return;
  }
}
int main(int c,char**v){char*M=v[1]; int NMAX=atoi(v[2]); int mir=c>3;
 for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*p=M+7*s+3*r; if(p[2]=='-'){NX[s][r]=-1;continue;} W[s][r]=p[0]-'0';MV[s][r]=p[1]=='R'?1:-1; if(mir)MV[s][r]=-MV[s][r]; NX[s][r]=p[2]-'A';}
 for(n=1;n<=NMAX;n++){ tried=0; rec(0,1); fprintf(stderr,"n=%d tried %lld %s\n",n,tried,found?"FOUND":""); if(found)break;}
 return 0;}
