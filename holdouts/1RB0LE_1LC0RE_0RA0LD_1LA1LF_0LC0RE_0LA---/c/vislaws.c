/* vislaws MACHINE STEPS SIDE ORIGIN W [FROM]
 * Token-level visit laws mined from a run from blank tape (C port of the F02 folder's laws.py, both sides).
 * SIDE R: the stream is the cells >= ORIGIN, cut into tokens of W cells [ORIGIN+W*i, ORIGIN+W*i+W).
 * SIDE L: the stream is the cells <= ORIGIN, tokens [ORIGIN-W*i-W+1, ORIGIN-W*i], read from the head outward
 *         (nearest cell first).
 * Each time the head enters a token from the stream's inner side (state q) and later leaves it back
 * through that side (state r), one row: q, token before (cells listed from the inner side outward), nested visits
 * of the rest as pairs entry/exit (exit in lower case), r, token after.  Only visits starting at step >= FROM count.
 * Output: one JSON row per line: [q, tok, calls, r, tok2, count, first]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int Wr[6][2],Mv[6][2],Nx[6][2];
#define MAXD 4096
typedef struct { char q; char tok[16]; char calls[512]; int nc; int live; } Frame;
typedef struct { char key[600]; long long cnt, first; } Row;
Row rows[20000]; int nrows=0;
void addrow(const char*k,long long step){ for(int i=0;i<nrows;i++) if(!strcmp(rows[i].key,k)){rows[i].cnt++;return;} strcpy(rows[nrows].key,k); rows[nrows].cnt=1; rows[nrows].first=step; nrows++; }
int main(int argc,char**argv){
  char*m=argv[1]; long long max=atoll(argv[2]); int side=argv[3][0]=='R'?1:-1; long long org=atoll(argv[4]); int W=atoi(argv[5]); long long from=argc>6?atoll(argv[6]):0;
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*t=m+7*s+3*r; if(t[0]=='-'){Nx[s][r]=-1;continue;} Wr[s][r]=t[0]-'0';Mv[s][r]=t[1]=='R'?1:-1;Nx[s][r]=t[2]-'A';}
  int N=1<<20; unsigned char*tp=calloc(N,1); long long p=N/2; int st=0; long long k=0; long long o=org+N/2;
  static Frame fr[MAXD];
  // token index of cell x: side R: (x-o)/W if x>=o else -1 ; side L: (o-x)/W if x<=o else -1
  #define TOK(x) (side>0 ? ((x)>=o ? ((x)-o)/W : -1) : ((x)<=o ? (o-(x))/W : -1))
  while(k<max){int r=tp[p];int nx=Nx[st][r]; if(nx<0){fprintf(stderr,"HALT %lld\n",k+1);break;}
    tp[p]=Wr[st][r]; long long q=p+Mv[st][r]; int i=TOK(p), j=TOK(q);
    if(j>i){ // entering token j from inner side
      if(i>=0 && fr[i].live && fr[i].nc<500){ fr[i].calls[fr[i].nc++]='A'+nx; fr[i].calls[fr[i].nc]=0; }
      if(j<MAXD){ Frame*f=&fr[j]; f->q='A'+nx; f->nc=0; f->calls[0]=0; f->live = k+1>=from;
        for(int c=0;c<W;c++){ long long x = side>0 ? o+W*j+c : o-W*j-c; f->tok[c]='0'+tp[x]; } f->tok[W]=0; }
    } else if(j<i){ // leaving token i to inner side
      if(i<MAXD && fr[i].live){ Frame*f=&fr[i]; char t2[16]; for(int c=0;c<W;c++){ long long x = side>0 ? o+W*i+c : o-W*i-c; t2[c]='0'+tp[x]; } t2[W]=0;
        char key[600]; snprintf(key,600,"[\"%c\", \"%s\", \"%s\", \"%c\", \"%s\"",f->q,f->tok,f->calls,'A'+nx,t2); addrow(key,k); }
      if(i<MAXD) fr[i].live=0;
      if(j>=0 && fr[j].live && fr[j].nc<500){ fr[j].calls[fr[j].nc++]='a'+nx; fr[j].calls[fr[j].nc]=0; }
    }
    p=q; st=nx; k++;
  }
  for(int i=0;i<nrows;i++) printf("%s, %lld, %lld]\n",rows[i].key,rows[i].cnt,rows[i].first);
}
