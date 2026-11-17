// evdiff X Y MIRROR SIDE NEV R [LIM] [MODE] [EVERY]: compare the tapes of two machines at their new-extreme events
// on one side, each X event against Y's events within R of the matched index; prints the differing middle words
// (MODE 1: summary counts, MODE 2: every EVERY-th event).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct{int w[6][2],d[6][2],s[6][2]; unsigned char*t; long long h,lo,hi,SZ; int st; long long steps; int halted;} M;
void init(M*m,const char*t,int mir){for(int i=0;i<6;i++)for(int y=0;y<2;y++){const char*p=t+7*i+3*y; if(p[2]=='-'){m->s[i][y]=-1;m->w[i][y]=1;m->d[i][y]=1;} else {m->w[i][y]=p[0]-'0';m->d[i][y]=(p[1]=='R'?1:-1)*(mir?-1:1);m->s[i][y]=p[2]-'A';}}
 m->SZ=1<<23; m->t=calloc(m->SZ,1); m->h=m->lo=m->hi=m->SZ/2; m->st=0; m->steps=0; m->halted=0;}
int next(M*m,int side,long long lim){ while(m->steps<lim){ int y=m->t[m->h]; int ns=m->s[m->st][y]; if(ns<0){m->halted=1;return 0;}
  m->t[m->h]=m->w[m->st][y]; m->h+=m->d[m->st][y]; m->st=ns; m->steps++; if(m->h<2||m->h>m->SZ-3) return 0;
  if(m->h<m->lo){m->lo=m->h; if(side==0) return 1;} else if(m->h>m->hi){m->hi=m->h; if(side==1) return 1;} } return 0;}
#define MAXL (1<<20)
int R; unsigned char *ring; long long *rlen; int *rst; long long *rsteps;
void snap(M*m,int side,unsigned char*b,long long*l){ long long n=m->hi-m->lo+1; if(n>MAXL)n=MAXL; *l=n; if(side==0) memcpy(b,m->t+m->lo,n); else for(long long i=0;i<n;i++)b[i]=m->t[m->hi-i]; }
int main(int argc,char**argv){ M X,Y; int mir=atoi(argv[3]), side=atoi(argv[4]); long NEV=atol(argv[5]); R=atoi(argv[6]); long long LIM=argc>7?atoll(argv[7]):4000000000LL;
 init(&X,argv[1],0); init(&Y,argv[2],mir); int W=2*R+1; ring=malloc((size_t)W*MAXL); rlen=calloc(W,8); rst=calloc(W,4); rsteps=calloc(W,8);
 static unsigned char bx[MAXL];
 long ny=0; // number of Y events snapped; slot = idx % W
 for(int i=0;i<=R;i++){ if(!next(&Y,side,LIM)){printf("Y end early\n");return 0;} snap(&Y,side,ring+(size_t)(ny%W)*MAXL,&rlen[ny%W]); rst[ny%W]=Y.st; rsteps[ny%W]=Y.steps; ny++; }
 long cur=0; long small=0,mid=0,tot=0,zero=0; int summ=argc>8?atoi(argv[8]):0; char last[300]=""; long same=0; long long lastna=-1,lastnb=-1;
 for(long e=0;e<NEV;e++){
  if(!next(&X,side,LIM)){if(!summ)printf("X stop e=%ld halted=%d steps=%lld\n",e,X.halted,X.steps);break;}
  long long lx; snap(&X,side,bx,&lx);
  long best=-1; long long bp=0,bs=0,bscore=1LL<<60;
  for(long j=cur-R;j<=cur+R;j++){ if(j<0||j>=ny||j<ny-W) continue; unsigned char*by=ring+(size_t)(j%W)*MAXL; long long ly=rlen[j%W];
    long long p=0; while(p<lx&&p<ly&&bx[p]==by[p])p++; long long s=0; while(s<lx-p&&s<ly-p&&bx[lx-1-s]==by[ly-1-s])s++;
    long long sc=(lx-p-s)+(ly-p-s)+(rst[j%W]!=X.st?0:0); if(sc<bscore){bscore=sc;best=j;bp=p;bs=s;} }
  if(best>=0) cur=best+1; else cur++;
  while(ny<=cur+R){ if(!next(&Y,side,LIM)){if(!summ)printf("Y stop at X e=%ld halted=%d steps=%lld\n",e,Y.halted,Y.steps); goto out;} snap(&Y,side,ring+(size_t)(ny%W)*MAXL,&rlen[ny%W]); rst[ny%W]=Y.st; rsteps[ny%W]=Y.steps; ny++; }
  unsigned char*by=ring+(size_t)(best%W)*MAXL; long long ly=rlen[best%W]; long long na=lx-bp-bs, nb=ly-bp-bs;
  char key[300]; int k=0; for(long long i=0;i<na&&i<40;i++)key[k++]='0'+bx[bp+i]; key[k++]='/'; for(long long i=0;i<nb&&i<40;i++)key[k++]='0'+by[bp+i]; key[k]=0;
  tot++; if(na+nb==0)zero++; if(na+nb<=16)small++; if(na+nb<=64)mid++;
  if(summ==2){ if(e%(argc>9?atol(argv[9]):100)==0) printf("e=%ld X=%lld Y=%lld p=%lld s=%lld len=%lld/%lld st%c%c %s\n",e,X.steps,rsteps[best%W],bp,bs,lx,ly,'A'+X.st,'A'+rst[best%W],key); continue;}
  if(summ) continue;
  if(strcmp(key,last)==0) same++; else { if(e>0) printf(" x%ld\n",same); same=1; strcpy(last,key);
    printf("e=%ld j=%ld X=%lld Y=%lld p=%lld s=%lld len=%lld/%lld st%c%c |a|=%lld |b|=%lld %s",e,best,X.steps,rsteps[best%W],bp,bs,lx,ly,'A'+X.st,'A'+rst[best%W],na,nb,key);}
 }
 out: if(!summ) printf(" x%ld\n",same); else printf("SUM zero=%ld tot=%ld small=%ld mid=%ld Xsteps=%lld Ysteps=%lld haltX=%d haltY=%d\n",zero,tot,small,mid,X.steps,Y.steps,X.halted,Y.halted);
}
