/* crun MACHINE MAXSTEPS S L|R MAXP [skip] [prefix]
   each time head in state S (or any state if S='*') is at the left/right end of visited region: print step and
   compressed tape (greedy periodic words up to MAXP, reps>=3, or >=2 when p>=3). skip: print every skip-th event.
   prefix: only print events whose expanded tape (head marked as X>) starts with prefix. */
#include "../../../tools/c/tm.h"
static char *buf; static long long bufn;
int main(int argc,char**argv){
  tm_machine m; tm_parse(argv[1],&m); long long max=atoll(argv[2]); int S=argv[3][0]=='*'?-1:argv[3][0]-'A'; int R=argv[4][0]=='R';
  int maxp=atoi(argv[5]); long long skip=argc>6?atoll(argv[6]):1; const char*pre=argc>7?argv[7]:"";
  tm_tape t; tm_tape_init(&t,1<<20); int st=0; long long ev=0;
  bufn=1<<20; buf=malloc(bufn);
  for(long long k=1;k<=max;k++){
    if(!tm_step(&m,&t,&st)){printf("halted %lld\n",k);return 0;}
    if((S<0||st==S)&&((R&&t.head==t.hi)||(!R&&t.head==t.lo))){
      ev++; if(ev%skip) continue;
      long long n=t.hi-t.lo+1; if(n+10>bufn){bufn=2*(n+10);buf=realloc(buf,bufn);}
      for(long long p=t.lo;p<=t.hi;p++) buf[p-t.lo]='0'+tm_get(&t,p);
      long long h=t.head-t.lo;
      /* prefix check */
      if(*pre){ char tmp[256]; int L=0; for(long long i=0;i<n&&L<200;i++){ if(i==h){tmp[L++]='A'+st;tmp[L++]='>';} tmp[L++]=buf[i]; } tmp[L]=0; if(strncmp(tmp,pre,strlen(pre))) continue; }
      printf("%lld",k);
      long long i=0; int lit=0;
      while(i<n){
        if(i==h){ printf(" %c>%c",'A'+st,buf[i]); i++; lit=0; continue; }
        int bp=0; long long br=0;
        for(int p=1;p<=maxp;p++){ long long r=1; long long lim=(h>i? h : n);
          while(i+(r+1)*p<=lim && !memcmp(buf+i,buf+i+r*p,p)) r++;
          if((r>=3||(p>=3&&r>=2)) && p*r>bp*br){bp=p;br=r;} }
        if(bp){ printf(" (%.*s)^%lld",bp,buf+i,br); i+=bp*br; lit=0; }
        else { if(!lit) putchar(' '); putchar(buf[i]); i++; lit=1; }
      }
      putchar('\n');
    }
  }
  printf("running %lld\n",max); return 0;
}
