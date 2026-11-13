// macro simulator of 1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF: blocks of 1s, one sweep at a time
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll; typedef __int128 i128;
#define MAXB 4096
ll buf[MAXB]; int OFF=2048; // n[i] = buf[OFF+i], i in [lo..hi)
static void pr128(i128 x){char s[64];int i=63;s[i]=0;if(!x){printf("0");return;}while(x){s[--i]='0'+(int)(x%10);x/=10;}printf("%s",s+i);}
int main(int argc,char**argv){
  ll N=atoll(argv[1]); int verbose=argc>2;
  int lo=OFF,hi=OFF; buf[hi++]=3; i128 T=6; ll S=0;
  for(S=0;S<N;S++){
    // sweep: new block 0 at hi, wall block 0 at lo-1
    buf[hi]=0; buf[lo-1]=0; int j=hi-1; i128 st=1; int top=hi+1; int wall=0; ll arr=-1;
    while(1){
      ll v=buf[j], h=v/2;
      if(j==lo && arr<0) arr=v;
      if(j==lo-1){ lo--; buf[lo-1]=0; wall=1; }
      buf[j-1]+=h; buf[j+1]+=h;
      // rounds cost: sum over b=v,v-2,...,>=2 of (b==2?8:2b+5)
      { ll r=v/2; if(r>0){ // b = v-2i, i=0..r-1 ; b>=2
          i128 s=(i128)r*(2*(i128)v+5) - (i128)2*2*((i128)r*(r-1)/2);
          if(v%2==0) s-=1; // the b=2 round costs 8 instead of 9
          st+=s; } }
      if(v%2==0){
        if(v==0){ printf("HALT v=0 sweep %lld\n",S); return 0;}
        buf[j]=0; j--; continue; }
      if(j-1==lo-1 && buf[lo-1]==0){ printf("HALT (wall, v=1) sweep %lld steps ",S); pr128(T+st); printf("\n"); return 0;}
      buf[j+1]+=3;
      memmove(&buf[j],&buf[j+1],sizeof(ll)*(top-j-1)); top--;
      st+=8; for(int i=j;i<top;i++) st+=buf[i]+1; st+=1;
      break;
    }
    hi=top; if(buf[lo-1]!=0) lo--; // wall block got h
    while(buf[hi-1]==0) hi--;
    while(buf[lo]==0) lo++;
    T+=st;
    if(wall||verbose){ printf("sweep %lld steps ",S); pr128(T); printf(" arrival %lld len %d first %lld %lld %lld\n",arr,hi-lo,buf[lo],buf[lo+1],buf[lo+2]); fflush(stdout);}
    if(lo<10||hi>MAXB-10){printf("overflow\n");return 1;}
  }
  printf("done %lld sweeps, steps ",S); pr128(T); printf(", %d blocks:",hi-lo);
  for(int i=lo;i<hi;i++) printf(" %lld",buf[i]); printf("\n");
}
