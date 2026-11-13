// Macro simulator for 1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA (works for any 6-state machine): blocks of K cells in
// run-length stacks, so a sweep over a long periodic stretch is one move.  Built and driven by py/epochs.py.
// usage: mrun MACHINE K STEPS MODE [TAPE STATE [DIR]]   mode 0: print left records; 1: also excursion depths;
// 2: stop at the first new leftmost cell (after the first 3 excursions) and print the whole tape; "exc" counts the
// right-end records at even positions (the excursions of 77294), "records" all right-end records (macro blocks of K cells).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned __int128 u128;
int K; int T[6][2][3]; // write, move(+1/-1), next (-1 halt)
typedef struct {uint32_t x; uint64_t c;} run;
run *L,*R; long nl,nr,capl,capr;
int cq[6][1<<12][2][4]; char cv[6][1<<12][2]; // result: q2,y,d2,n ; valid
static void push(run **st,long *n,long *cap,uint32_t x,uint64_t c){
  if(*n>1 && (*st)[*n-1].x==x){(*st)[*n-1].c+=c;return;}
  if(*n>=*cap){*cap*=2;*st=realloc(*st,*cap*sizeof(run));}
  (*st)[*n].x=x;(*st)[*n].c=c;(*n)++;
}
int main(int argc,char**argv){
  char*m=argv[1]; K=atoi(argv[2]); double S=atof(argv[3]); int mode=argc>4?atoi(argv[4]):0;
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*t=m+7*s+3*r; if(t[0]=='-'){T[s][r][2]=-1;continue;} T[s][r][0]=t[0]-'0';T[s][r][1]=t[1]=='R'?1:-1;T[s][r][2]=t[2]-'A';}
  capl=capr=1024;L=malloc(capl*sizeof(run));R=malloc(capr*sizeof(run));nl=nr=1;L[0].x=0;L[0].c=1;R[0].x=0;R[0].c=1;
  int q=0,d=1; long long pos=0,minpos=0,maxpos=0,exmin=0,deep=1LL<<60; uint64_t nex=0,nrec=0,lastreset=0; int armed=0;
  if(argc>5){ // initial tape: cells string, head right after it, state argv[6]
    char*s=argv[5]; int n=strlen(s); int pad=(K-n%K)%K; q=argv[6][0]-'A'; d=1;
    for(int i=0;i<n+pad;i+=K){ uint32_t x=0; for(int j=0;j<K;j++){int idx=i+j-pad; int b= idx>=0? s[idx]-'0':0; x|=(uint32_t)b<<j;} push(&L,&nl,&capl,x,1);} 
    minpos=-n; }
  if(argc>7){ // init mode R: string on the right stack, head at its left end, state argv[6], dir argv[7] (L/R)
    nl=1; char*s=argv[5]; int n=strlen(s); int pad=(K-n%K)%K; q=argv[6][0]-'A'; d=argv[7][0]=='R'?1:-1;
    for(int i=n+pad-K;i>=0;i-=K){ uint32_t x=0; for(int j=0;j<K;j++){int idx=i+j; int b= idx<n? s[idx]-'0':0; x|=(uint32_t)b<<j;} push(&R,&nr,&capr,x,1);} 
    minpos=0; maxpos=n; } u128 steps=0; uint64_t ms=0; u128 lim=(u128)S;
  memset(cv,0,sizeof cv);
  while(steps<lim){
    run **fr=d==1?&R:&L; long *nf=d==1?&nr:&nl; long *cf=d==1?&capr:&capl;
    run **bk=d==1?&L:&R; long *nb=d==1?&nl:&nr; long *cb=d==1?&capl:&capr;
    uint32_t x=(*fr)[*nf-1].x;
    if(*nf>1){ if(--(*fr)[*nf-1].c==0) (*nf)--; }
    int di=d==1?0:1;
    if(!cv[q][x][di]){
      int c[16]; for(int i=0;i<K;i++) c[i]=(x>>i)&1;
      int i=d==1?0:K-1, qq=q, n=0, halt=0;
      while(i>=0&&i<K){ if(T[qq][c[i]][2]<0){halt=1;break;} int w=T[qq][c[i]][0],mv=T[qq][c[i]][1],nq=T[qq][c[i]][2]; c[i]=w;i+=mv;qq=nq;n++; if(n>10000){fprintf(stderr,"loop\n");return 1;} }
      uint32_t y=0; for(int j=0;j<K;j++) y|=(uint32_t)c[j]<<j;
      if(halt){ printf("HALT after %.0f+%d steps, pos %lld minpos %lld\n",(double)steps,n+1,pos,minpos); return 0;}
      cq[q][x][di][0]=qq;cq[q][x][di][1]=y;cq[q][x][di][2]=i>=K?1:-1;cq[q][x][di][3]=n;cv[q][x][di]=1;
    }
    int q2=cq[q][x][di][0]; uint32_t y=cq[q][x][di][1]; int d2=cq[q][x][di][2]; int n=cq[q][x][di][3];
    ms++;
    if(q2==q&&d2==d){
      uint64_t c=1; if(*nf>1 && (*fr)[*nf-1].x==x){c+=(*fr)[*nf-1].c;(*nf)--;}
      steps+=(u128)c*n; push(bk,nb,cb,y,c); pos+=d*(long long)c*K;
    } else {
      steps+=n; if(d2==d) pos+=d*K;
      if(d2==1) push(&L,&nl,&capl,y,1); else push(&R,&nr,&capr,y,1);
    }
    q=q2;d=d2;
    if(pos<exmin) exmin=pos;
    if(pos>maxpos){ maxpos=pos; nrec++; if(maxpos%2==0){ nex++; if(exmin<deep && nex>lastreset+600){deep=exmin; if(mode==1) {printf("deep %lld (from left %lld) at excursion %llu steps %.6e\n",deep,deep-minpos,(unsigned long long)nex,(double)steps); fflush(stdout);} } exmin=pos; } }
    if(mode==3 && armed && q==0 && d==1 && nr==1){
      printf("RESTART steps %.0f exc %llu tape ",(double)steps,(unsigned long long)nex);
      for(long i=1;i<nl;i++) for(uint64_t c=0;c<L[i].c;c++) for(int j=0;j<K;j++) putchar('0'+((L[i].x>>j)&1));
      printf("\n"); return 0; }
    if(pos<minpos && mode==3) armed=1;
    if(pos<minpos && mode==2 && nex<3) minpos=pos;
    if(pos<minpos && mode==2){
      printf("LEFTREC steps %.0f exc %llu state %c dir %c tape ",(double)steps,(unsigned long long)nex,'A'+q,d==1?'R':'L');
      for(long i=1;i<nl;i++) for(uint64_t c=0;c<L[i].c;c++) for(int j=0;j<K;j++) putchar('0'+((L[i].x>>j)&1));
      putchar('|');
      for(long i=nr-1;i>0;i--) for(uint64_t c=0;c<R[i].c;c++) for(int j=0;j<K;j++) putchar('0'+((R[i].x>>j)&1));
      printf(" records %llu\n",(unsigned long long)nrec); return 0; }
    if(pos<minpos){ minpos=pos; deep=1LL<<60; lastreset=nex; if(mode==1) printf("LEFT %lld steps %.6e\n",pos,(double)steps);
      if(mode==0){ printf("max %lld %.6e %llu %lld runs %ld+%ld :",maxpos,(double)steps,(unsigned long long)ms,pos,nl-1,nr-1);
        // print left part nearest-to-far? print leftmost runs of whole tape: left stack bottom..top then right
        int cnt=0; for(long i=1;i<nl && cnt<8;i++,cnt++){printf(" ");for(int j=0;j<K;j++)putchar('0'+((L[i].x>>j)&1));printf("^%llu",(unsigned long long)L[i].c);}
        if(nl<=8){printf(" |"); for(long i=nr-1;i>0 && cnt<12;i--,cnt++){printf(" ");for(int j=0;j<K;j++)putchar('0'+((R[i].x>>j)&1));printf("^%llu",(unsigned long long)R[i].c);}}
        printf("\n"); fflush(stdout);}
    }
  }
  printf("END %.6e steps %llu msteps pos %lld minpos %lld runs %ld %ld\n",(double)steps,(unsigned long long)ms,pos,minpos,nl,nr);
  return 0;
}
