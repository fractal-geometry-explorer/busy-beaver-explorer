// cfgmatch M1 M2 MAP MIRROR N [abs]
//
// Do two machines, each run N steps from blank tape, ever reach a common configuration?
//
// MAP has six characters: MAP[s] is the state of M2 that state s of M1 is read as ('-': none; the word
// "blind" compares tape and head only, whatever the states). With MIRROR = 1 the tape of M1 is reflected.
// Configurations are compared up to a shift of the tape, or at their absolute positions with "abs".
// Each configuration is a 61-bit polynomial hash of the tape around the head, updated in O(1) a step; the two
// lists are sorted and intersected. Equal hashes of different configurations are possible in principle (about
// 4e-5 expected over 10^14 comparisons), so a count of 0 is exact and a positive count is evidence.
//
// Output, one line: the count, the first and last matching step pairs (step of M1, step of M2), whether the
// matches come in the same order in both runs, and the longest gaps between matches.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned __int128 u128; typedef uint64_t u64;
#define P ((1ULL<<61)-1)
static u64 mm(u64 a,u64 b){u128 t=(u128)a*b; u64 r=(u64)(t&P)+(u64)(t>>61); if(r>=P)r-=P; return r;}
static u64 pw(u64 a,u64 e){u64 r=1; while(e){if(e&1)r=mm(r,a); a=mm(a,a); e>>=1;} return r;}
typedef struct{int w,d,n;} tr;
static void parse(const char*m,tr T[6][2]){for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*t=m+7*s+3*b; if(t[0]=='-'){T[s][b].n=-1;} else {T[s][b].w=t[0]-'0';T[s][b].d=t[1]=='R'?1:-1;T[s][b].n=t[2]-'A';}}}
typedef struct{u64 h; u64 step;} rec;
static int cmp(const void*a,const void*b){u64 x=((rec*)a)->h,y=((rec*)b)->h; return x<y?-1:x>y; }
#define X 1000003ULL
static u64 XI; static int blind=0;
static u64 mix(u64 h,int s){ return h*8+ (u64)s; }
// returns count; fills recs. smap: state map; mir; absmode
static long run(const char*m,const char*smap,int mir,int absmode,long N,rec*R){
  tr T[6][2]; parse(m,T); long W=2*N+10; unsigned char*tape=calloc(W,1); long h=N+5; int s=0; long cnt=0;
  // translation-invariant: H=sum t[i]*X^(i-h), Hb=sum t[i]*X^(h-i)
  // abs: Ha=sum t[i]*X^(i-h0) tracked via cur power pwf=X^(h-h0), pwb=X^(h0-h); Hma mirrored
  u64 H=0,Hb=0,Ha=0,Hma=0,pf=1,pb=1; long h0=h;
  for(long t=0;t<=N;t++){
    int ms = blind?0:(smap? (smap[s]==45?-1:smap[s]-65) : s);
    if(ms>=0){
      u64 key;
      if(absmode){ key = mix(mir?Hma:Ha, ms) ^ ((u64)(mir? h0-h : h-h0)*0x9E3779B97F4A7C15ULL); }
      else key = mix(mir?Hb:H, ms);
      R[cnt].h=key; R[cnt].step=t; cnt++;
    }
    if(t==N)break;
    int b=tape[h]; tr x=T[s][b]; if(x.n<0){fprintf(stderr,"HALT %s at %ld\n",m,t);break;}
    if(x.w!=b){ if(x.w){H=(H+1)%P;Hb=(Hb+1)%P;Ha=(Ha+pf)%P;Hma=(Hma+pb)%P;} else {H=(H+P-1)%P;Hb=(Hb+P-1)%P;Ha=(Ha+P-pf)%P;Hma=(Hma+P-pb)%P;} tape[h]=x.w; }
    if(x.d>0){ H=mm(H,XI); Hb=mm(Hb,X); pf=mm(pf,X); pb=mm(pb,XI); h++; }
    else { H=mm(H,X); Hb=mm(Hb,XI); pf=mm(pf,XI); pb=mm(pb,X); h--; }
    s=x.n;
  }
  free(tape); return cnt;
}
int main(int c,char**v){
  XI=pw(X,P-2);
  const char*m1=v[1],*m2=v[2],*map=v[3]; if(map[0]==98)blind=1; int mir=atoi(v[4]); long N=atol(v[5]); int absmode=c>6;
  rec*R1=malloc(sizeof(rec)*(N+1)),*R2=malloc(sizeof(rec)*(N+1));
  long n1=run(m1,map,mir,absmode,N,R1), n2=run(m2,NULL,0,absmode,N,R2);
  qsort(R1,n1,sizeof(rec),cmp); qsort(R2,n2,sizeof(rec),cmp);
  long i=0,j=0,cnt=0;
  // collect matches (hash values are distinct within a run unless the run repeats a configuration)
  long cap=N+1, nm=0; rec*Mt=malloc(sizeof(rec)*cap);
  while(i<n1&&j<n2){ if(R1[i].h<R2[j].h)i++; else if(R1[i].h>R2[j].h)j++; else { cnt++; if(nm<cap){Mt[nm].h=R1[i].step;Mt[nm].step=R2[j].step;nm++;} i++; j++; } }
  qsort(Mt,nm,sizeof(rec),cmp);
  printf("%s %s %s mir=%d N=%ld %s matches=%ld", m1,m2,map,mir,N,absmode?"abs":"transl",cnt);
  // skip the trivial t=0 blank-tape match if states coincide
  for(long k=0;k<nm&&k<4;k++)printf(" (%llu,%llu)",(unsigned long long)Mt[k].h,(unsigned long long)Mt[k].step);
  if(nm>4)printf(" ... (%llu,%llu)",(unsigned long long)Mt[nm-1].h,(unsigned long long)Mt[nm-1].step);
  { int mono=1; u64 g1=0,g2=0; for(long k=1;k<nm;k++){ if(Mt[k].step<=Mt[k-1].step)mono=0; if(Mt[k].h-Mt[k-1].h>g1)g1=Mt[k].h-Mt[k-1].h; if(Mt[k].step>Mt[k-1].step&&Mt[k].step-Mt[k-1].step>g2)g2=Mt[k].step-Mt[k-1].step;} if(nm>1)printf(" monotone=%d maxgap1=%llu maxgap2=%llu",mono,(unsigned long long)g1,(unsigned long long)g2); }
  printf("\n"); return 0;
}
