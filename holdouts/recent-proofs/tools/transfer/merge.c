// merge TABLE X T : does the run of TABLE from blank tape in state X meet the run from state A (same table)?
// hashes of configurations relative to the head, sampled by the hash alone (1/64), both runs T steps.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned __int128 u128; typedef uint64_t u64;
#define P ((1ULL<<61)-1)
static inline u64 mm(u64 a,u64 b){u128 t=(u128)a*b; u64 lo=(u64)(t&P), hi=(u64)(t>>61); u64 s=lo+hi; if(s>=P)s-=P; return s;}
static u64 pw(u64 a,u64 e){u64 r=1; while(e){if(e&1)r=mm(r,a); a=mm(a,a); e>>=1;} return r;}
#define TL (1u<<28)
static uint8_t *tape; int w[12],mv[12],ns[12];
static u64 *tab; static u64 TM_; // open addressing set
static void ins(u64 k){u64 i=(k*0x9E3779B97F4A7C15ULL)>>(64-27); while(tab[i]&&tab[i]!=k)i=(i+1)&((1u<<27)-1); tab[i]=k;}
static int has(u64 k){u64 i=(k*0x9E3779B97F4A7C15ULL)>>(64-27); while(tab[i]){if(tab[i]==k)return 1;i=(i+1)&((1u<<27)-1);} return 0;}
int main(int argc,char**argv){
  char*m=argv[1]; int X=argv[2][0]-'A'; u64 T=(u64)atof(argv[3]);
  for(int i=0;i<6;i++)for(int b=0;b<2;b++){char*t=m+i*7+b*3;int k=i*2+b;
    if(t[0]=='-'){ns[k]=-1;w[k]=0;mv[k]=0;} else {w[k]=t[0]-'0';mv[k]=t[1]=='R'?1:-1;ns[k]=t[2]-'A';}}
  tape=malloc(TL); tab=calloc(1u<<27,8); u64 R=0x1234567890abcdefULL%P, RI=pw(R,P-2);
  u64 first=0,nhit=0,nsamp[2]={0,0}; long firstA=-1;
  for(int pass=0;pass<2;pass++){
    memset(tape,0,TL); long pos=TL/2; int s=pass==0?0:X; u64 h=0,rp=1,rip=1; u64 t; int halted=0;
    for(t=0;t<T;t++){
      u64 key=mm(h,rip); key=key*8+s+1;
      if(((key*0xD6E8FEB86659FD93ULL)>>58)==0){ nsamp[pass]++; if(pass==0){ if(nsamp[0]<60000000) ins(key);} else if(has(key)){ if(!nhit)first=t; nhit++; } }
      int k=s*2+tape[pos]; if(ns[k]<0){halted=1;break;}
      if(w[k]!=tape[pos]){ if(w[k]) {h+=rp; if(h>=P)h-=P;} else {h+=P-rp; if(h>=P)h-=P;} tape[pos]=w[k]; }
      if(mv[k]>0){pos++; rp=mm(rp,R); rip=mm(rip,RI);} else {pos--; rp=mm(rp,RI); rip=mm(rip,R);}
      s=ns[k]; if(pos<8||pos>TL-8)break;
    }
    printf("%s pass=%d start=%c steps=%llu halted=%d samples=%llu\n",m,pass,pass?'A'+X:'A',(unsigned long long)t,halted,(unsigned long long)nsamp[pass]);
  }
  printf("RESULT %s X=%c hits=%llu first_hit_step_of_X_run=%llu\n",m,'A'+X,(unsigned long long)nhit,(unsigned long long)first);
}
