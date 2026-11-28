// usage N < machines : per-transition use counts and last-use step
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define TL (1u<<28)
static uint8_t *tape;
int main(int argc,char**argv){
  uint64_t N=strtoull(argv[1],0,10); if(argc>1){double d=atof(argv[1]); N=(uint64_t)d;}
  tape=malloc(TL); char line[256];
  while(fgets(line,sizeof line,stdin)){
    char *m=line; if(strlen(m)<41) continue; m[41]=0;
    int w[12],mv[12],ns[12];
    for(int i=0;i<6;i++)for(int b=0;b<2;b++){char*t=m+i*7+b*3;int k=i*2+b;
      if(t[0]=='-'){ns[k]=-1;w[k]=0;mv[k]=0;} else {w[k]=t[0]-'0';mv[k]=t[1]=='R'?1:-1;ns[k]=t[2]-'A';}}
    memset(tape,0,TL); uint64_t cnt[12]={0},last[12]={0}; int64_t pos=TL/2,lo=pos,hi=pos; int s=0; uint64_t t=0; int halted=0,oob=0;
    // chunked: record counts per chunk to get last-use at chunk resolution
    uint64_t chunk=N/1000; if(chunk<1)chunk=1;
    while(t<N){
      uint64_t c2[12]={0}; uint64_t e=t+chunk; if(e>N)e=N;
      uint64_t tt=t;
      for(;tt<e;tt++){
        int k=s*2+tape[pos]; c2[k]++;
        if(ns[k]<0){halted=1;break;}
        tape[pos]=w[k]; pos+=mv[k]; s=ns[k];
        if(pos<16||pos>TL-16){oob=1;break;}
      }
      for(int k=0;k<12;k++) if(c2[k]){cnt[k]+=c2[k]; last[k]=tt;}
      t=tt; if(halted||oob)break;
    }
    printf("%s %llu %s",m,(unsigned long long)t,halted?"HALT":oob?"OOB":"run");
    for(int k=0;k<12;k++) printf(" %llu:%llu",(unsigned long long)cnt[k],(unsigned long long)last[k]);
    printf("\n"); fflush(stdout);
  }
}
