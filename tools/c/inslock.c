// inslock TABLE S N [CHECKEVERY] [v|q] [K] [MINLEN] [M1]: two runs of one table that differ by one inserted word.
// X = TABLE from state A on blank tape, Z = TABLE from state S.  Phase 1 takes the K-th pair of configurations (in the
// first M1 steps of each run) where one is the other with a word of at least MINLEN cells inserted.  Phase 2 follows
// the shorter run and the place and contents of the word, with the rules of tools/lean/TM/Insert.lean (`tnext`):
// a transparent crossing, else a shift, else BAD.  With NOEXC unset it also allows far-end excursions, which the Lean
// file does not cover; set NOEXC=1 to check exactly the Lean condition.  Every CHECKEVERY steps the longer run is
// simulated to the matching step and compared cell by cell (VERIFY FAIL if not).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int W[6][2],D[6][2],S[6][2]; long long shm[6][2];
typedef struct{unsigned char*t; long long h,lo,hi,SZ; int st; long long steps; int halted;} M;
void init(M*m,int st){m->SZ=1LL<<25; m->t=calloc(m->SZ,1); m->h=m->lo=m->hi=m->SZ/2; m->st=st; m->steps=0; m->halted=0;}
static inline int step(M*m){int y=m->t[m->h]; int ns=S[m->st][y]; if(ns<0){m->halted=1;return 0;} m->t[m->h]=W[m->st][y]; m->h+=D[m->st][y]; m->st=ns; m->steps++; if(m->h<m->lo)m->lo=m->h; if(m->h>m->hi)m->hi=m->h; return 1;}
int nextev(M*m,long long lim){ long long lo=m->lo,hi=m->hi; while(m->steps<lim){ if(!step(m))return 0; if(m->h<2||m->h>m->SZ-3)return 0; if(m->lo<lo||m->hi>hi) return 1;} return 0;}
int main(int argc,char**argv){
 const char*t=argv[1]; int s0=argv[2][0]-'A'; long long N=atoll(argv[3]); long long CK=argc>4?atoll(argv[4]):10000000; int verbose=argc>5 && argv[5][0]=='v'; int skip=argc>6?atoi(argv[6]):0; int minL=argc>7?atoi(argv[7]):1;
 for(int i=0;i<6;i++)for(int y=0;y<2;y++){const char*p=t+7*i+3*y; if(p[2]=='-'){S[i][y]=-1;W[i][y]=1;D[i][y]=1;} else {W[i][y]=p[0]-'0';D[i][y]=p[1]=='R'?1:-1;S[i][y]=p[2]-'A';}}
 M X,Z; init(&X,0); init(&Z,s0); M *sh=NULL,*lg=NULL; long long q=0; unsigned char v[256]; int L=0;
 // phase 1: snapshots of both runs for the first M1 steps; candidate = pure insertion with head consistent, k-th one
 long long M1=argc>8?atoll(argv[8]):20000;
 typedef struct{long long steps,lo,len,h; int st; unsigned char*tp;} Snap;
 Snap*sx=malloc(sizeof(Snap)*M1),*sz=malloc(sizeof(Snap)*M1); M*ms[2]={&X,&Z}; Snap*ss[2]={sx,sz}; long long cnt[2]={0,0};
 for(int w=0;w<2;w++){ M*m=ms[w]; for(long long i=0;i<M1;i++){ Snap*p=&ss[w][i]; long long l0=m->lo,h0=m->hi; while(l0<m->h && !m->t[l0]) l0++; while(h0>m->h && !m->t[h0]) h0--; p->steps=m->steps; p->lo=l0; p->len=h0-l0+1; p->h=m->h-l0; p->st=m->st; p->tp=malloc(p->len); memcpy(p->tp,m->t+l0,p->len); cnt[w]++; if(!step(m)) break; } }
 int found=0; long long fsx=0,fsz=0,fq=0; int fshort=0; 
 // enumerate by increasing max(i,j)
 for(long long Mx=0; Mx<M1 && !found; Mx++){
   for(int pass=0;pass<2 && !found;pass++) for(long long o=0;o<=Mx && !found;o++){
     long long i= pass==0? Mx:o, j= pass==0? o:Mx; if(pass==1 && o==Mx) continue; if(i>=cnt[0]||j>=cnt[1]) continue;
     Snap*a_=&sx[i],*b_=&sz[j]; if(getenv("DBG")&&i==2&&j==49){printf("dbg st %d %d len %lld %lld h %lld %lld\n",a_->st,b_->st,a_->len,b_->len,a_->h,b_->h);} if(a_->st!=b_->st || a_->len==b_->len) continue;
     Snap*c=a_->len<b_->len?a_:b_, *cp=a_->len<b_->len?b_:a_; long long d=cp->len-c->len; if(d<minL||d>200) continue;
     long long p=0; while(p<c->len && c->tp[p]==cp->tp[p]) p++; long long sfx=0; while(sfx<c->len-p && c->tp[c->len-1-sfx]==cp->tp[cp->len-1-sfx]) sfx++;
     if(p+sfx<c->len) continue;
     long long qq=-1; long long bd=-1; for(long long bb=c->len-sfx; bb<=p; bb++){ long long mp= c->h<bb? c->h : c->h+d; if(mp==cp->h){ long long dist= bb>c->h? bb-c->h : c->h-bb+1; if(dist>bd){bd=dist;qq=bb;} } }
     if(qq<0) continue; if(skip-->0) continue;
     found=1; fsx=i; fsz=j; fq=qq; fshort = (c==a_)?0:1; L=(int)d; for(int k=0;k<L;k++) v[k]=cp->tp[qq+k];
   }
 }
 if(!found){printf("no match\n");return 0;}
 // rebuild machines at the matched steps
 free(X.t); free(Z.t); init(&X,0); init(&Z,s0); while(X.steps<sx[fsx].steps) step(&X); while(Z.steps<sz[fsz].steps) step(&Z);
 sh= fshort==0? &X:&Z; lg= fshort==0? &Z:&X; q=(fshort==0?sx[fsx].lo:sz[fsz].lo)+fq;
 printf("match: short=%s steps %lld, long=%s steps %lld, state %c, |v|=%d v=",sh==&X?"A":"S",sh->steps,lg==&X?"A":"S",lg->steps,'A'+sh->st,L);
 for(int i=0;i<L;i++)putchar('0'+v[i]); printf(" q-lo=%lld len=%lld\n",fq,sh->hi-sh->lo+1);
 // phase 2: tracked run
 long long extra=lg->steps - sh->steps; // long steps = short steps + extra
 long long ncross=0,nshift=0; long long modes[6][2][1]={{{0}}}; long long lastck=sh->steps;
 char seen[64][300]; int nseen=0;
 while(sh->steps<N){
   int y=sh->t[sh->h]; int ns=S[sh->st][y];
   if(ns<0){ printf("short halts at %lld\n",sh->steps); break; }
   int dir=D[sh->st][y];
   int crossing = (dir==1 && sh->h==q-1) || (dir==-1 && sh->h==q);
   step(sh);
   if(crossing){ int st0=sh->st;
     // try transparent crossing from entry side
     unsigned char w[256]; memcpy(w,v,L); int pos = dir==1?0:L-1; int st=sh->st; long long n=0; int ok=0;
     while(n<100000){ int yy=w[pos]; int nn=S[st][yy]; if(nn<0) break; w[pos]=W[st][yy]; pos+=D[st][yy]; st=nn; n++; if(pos<0||pos>=L) break; }
     if(((dir==1&&pos>=L)||(dir==-1&&pos<0)) && st==sh->st){ ok=1; if(getenv("WIN") && (ncross<8 || ncross%5000==0)){ printf("cross#%lld %c%c step %lld: ",ncross,'A'+st,dir>0?'R':'L',sh->steps); for(long long i=sh->lo;i<q;i++)putchar('0'+sh->t[i]); printf(" | "); for(int i=0;i<L;i++)putchar('0'+w[i]); printf(" | "); for(long long i=q;i<q+40&&i<=sh->hi;i++)putchar('0'+sh->t[i]); printf("\n"); } memcpy(v,w,L); extra+=n; ncross++; modes[st][dir>0][0]++;
        if(verbose){ char key[300]; int k=sprintf(key,"%c%c ",'A'+st,dir>0?'R':'L'); for(int i=0;i<L;i++)key[k++]='0'+v[i]; key[k]=0; int f=0; for(int i=0;i<nseen;i++) if(!strcmp(seen[i],key)) f=1; if(!f&&nseen<64){strcpy(seen[nseen++],key); printf("crossing mode %s at %lld\n",key,sh->steps);} }
     }
     int blankb=1; if(dir==1){for(long long i=q;i<=sh->hi;i++) if(sh->t[i]){blankb=0;break;}} else {for(long long i=sh->lo;i<q;i++) if(sh->t[i]){blankb=0;break;}}
     if(!ok && blankb && !getenv("NOEXC")){
       // far-end excursion: short runs on its real tape (blank beyond) until the head comes back across the boundary
       long long ns_=0; int back=0;
       while(ns_<100000000){ int yy=sh->t[sh->h]; if(S[sh->st][yy]<0) break; step(sh); ns_++; if((dir==1&&sh->h<q)||(dir==-1&&sh->h>=q)){back=1;break;} }
       static unsigned char loc[1<<22]; long long LL=1<<22; memset(loc,0,LL); long long base= dir==1?16:LL-16-L; memcpy(loc+base,v,L);
       long long ph = dir==1? base : base+L-1; int st2=st0; long long nl=0; int back2=0;
       while(nl<200000000){ int yy=loc[ph]; int nn=S[st2][yy]; if(nn<0) break; loc[ph]=W[st2][yy]; ph+=D[st2][yy]; st2=nn; nl++; if(ph<0||ph>=LL) break; if((dir==1&&ph<base)||(dir==-1&&ph>base+L-1)){back2=1;break;} }
       if(back&&back2&&st2==sh->st){
         long long span = dir==1? (sh->hi-q+1) : (q-sh->lo); if(span<0)span=0; int matched=0;
         for(long long j=0;j<=span && !matched;j++){
           int match=1;
           for(long long i=0;i<span+L+4 && match;i++){
             // long cell i beyond boundary (in direction) vs short: i<j -> short i ; j<=i<j+L -> v' ; i>=j+L -> short i-L
             int b_= dir==1? loc[base+i] : loc[base+L-1-i];
             if(i<j){ int a_= dir==1? sh->t[q+i] : sh->t[q-1-i]; if(a_!=b_) match=0; }
             else if(i>=j+L){ long long ii=i-L; int a_= dir==1? sh->t[q+ii] : sh->t[q-1-ii]; if(a_!=b_) match=0; }
           }
           if(match){ matched=1; ok=1;
             if(dir==1){ for(int k2=0;k2<L;k2++) v[k2]=loc[base+j+k2]; q=q+j; } else { for(int k2=0;k2<L;k2++) v[k2]=loc[base+L-1-j-(L-1)+k2]; q=q-j; }
             extra+=nl-ns_; ncross++; modes[st0][dir>0][0]++;
             if(verbose){printf("excursion %c%c at %lld: %lld/%lld steps j=%lld v=",'A'+st0,dir>0?'R':'L',sh->steps,ns_,nl,j); for(int i=0;i<L;i++)putchar('0'+v[i]); printf("\n");}
           }
         }
         if(matched) continue;
       }
       printf("BAD excursion at %lld: back %d %d states %c %c\n",sh->steps,back,back2,'A'+sh->st,'A'+st2); break;
     }
     if(!ok){ // shift boundary along the head's direction
       // head is now at q (dir=1) or q-1 (dir=-1) in short; shift boundary past it if cell matches
       if(dir==1 && sh->t[q]==v[0]){ shm[sh->st][1]++; unsigned char f=v[0]; memmove(v,v+1,L-1); v[L-1]=f; q++; nshift++; }
       else if(dir==-1 && sh->t[q-1]==v[L-1]){ shm[sh->st][0]++; unsigned char f=v[L-1]; memmove(v+1,v,L-1); v[0]=f; q--; nshift++; }
       else { printf("BAD at short step %lld: state %c dir %d, crossing not transparent and no shift; v=",sh->steps,'A'+sh->st,dir); for(int i=0;i<L;i++)putchar('0'+v[i]); printf(" (crossing gave pos %d state %c after %lld)\n",pos,'A'+st,n); break; }
     }
   }
   if(sh->steps-lastck>=CK){ lastck=sh->steps;
     long long target=sh->steps+extra; while(lg->steps<target){ if(!step(lg)){printf("long halted?!\n");return 1;} }
     // compare: lg tape = sh tape with v at q
     int st_ok = lg->st==sh->st; long long hm = sh->h<q? sh->h : sh->h+L; long long off = lg->h - hm; int tap_ok=1;
     long long a=sh->lo<lg->lo-off?sh->lo:lg->lo-off; long long b=sh->hi>lg->hi-off-L?sh->hi:lg->hi-off-L;
     for(long long i=a-2;i<=b+2 && tap_ok;i++){ int cs = i<q? sh->t[i] : -1; if(i<q){ if(lg->t[i+off]!=cs) tap_ok=0; } else { if(lg->t[i+L+off]!=sh->t[i]) tap_ok=0; } }
     for(int i=0;i<L&&tap_ok;i++) if(lg->t[q+i+off]!=v[i]) tap_ok=0;
     if(!st_ok||!tap_ok){ printf("VERIFY FAIL at %lld st_ok %d tap_ok %d\n",sh->steps,st_ok,tap_ok); return 1; }
   }
 }
 printf("END short steps %lld long steps(est) %lld crossings %lld shifts %lld q-lo %lld hi-q %lld v=",sh->steps,sh->steps+extra,ncross,nshift,q-sh->lo,sh->hi-q); for(int i=0;i<L;i++)putchar('0'+v[i]); printf("\nshifts:"); for(int i=0;i<6;i++)for(int j=0;j<2;j++) if(shm[i][j]) printf(" %c%c:%lld",'A'+i,j?'R':'L',shm[i][j]); printf("\nmodes:"); for(int i=0;i<6;i++)for(int j=0;j<2;j++) if(modes[i][j][0]) printf(" %c%c:%lld",'A'+i,j?'R':'L',modes[i][j][0]); printf("\n");
}
