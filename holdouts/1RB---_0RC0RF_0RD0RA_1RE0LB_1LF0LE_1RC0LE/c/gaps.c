/* gaprun MACHINE MAXSTEPS S L|R [skip] [maxlines]: at each event (state S at the left/right end), print
   step, then the gaps between consecutive 1s (number of 0s), run-length coded: g^n ; first token = zeros from left end to first 1 (head at left end) */
#include "../../../tools/c/tm.h"
int main(int argc,char**argv){
  tm_machine m; tm_parse(argv[1],&m); long long max=atoll(argv[2]); int S=argv[3][0]=='*'?-1:argv[3][0]-'A'; int R=argv[4][0]=='R';
  long long skip=argc>5?atoll(argv[5]):1; long long maxl=argc>6?atoll(argv[6]):1LL<<60;
  tm_tape t; tm_tape_init(&t,1<<20); int st=0; long long ev=0, lines=0;
  for(long long k=1;k<=max;k++){
    if(!tm_step(&m,&t,&st)){printf("halted %lld\n",k);return 0;}
    if((S<0||st==S)&&((R&&t.head==t.hi)||(!R&&t.head==t.lo))){
      ev++; if(ev%skip) continue; if(++lines>maxl) break;
      printf("%lld %c:",k,'A'+st);
      long long p=t.lo, prev=0; int first=1; long long g=-1, cnt=0;
      for(;p<=t.hi;p++){ if(tm_get(&t,p)){ long long gap = first? p-t.lo : p-prev-1; prev=p; first=0;
          if(gap==g) cnt++; else { if(cnt) { if(cnt>1) printf(" %lld^%lld",g,cnt); else printf(" %lld",g);} g=gap; cnt=1; } } }
      if(cnt){ if(cnt>1) printf(" %lld^%lld",g,cnt); else printf(" %lld",g);}
      printf(" | %lld\n", t.hi-prev);
    }
  }
  return 0;
}
