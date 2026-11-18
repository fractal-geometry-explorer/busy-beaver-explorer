/* tapeat: the tape at step N of the run from blank tape: "SNAP N HEAD_OFFSET STATE CELLS" (cells from the first to the
 * last 1, widened to include the head; HALT STEPS if it halts first). Used to check tools/c/slicememo.cpp. */
#include "tm.h"
int main(int c,char**v){tm_machine m; tm_parse(v[1],&m); long long N=atoll(v[2]);
 tm_tape t; tm_tape_init(&t,1<<20); int st=0;
 for(long long i=0;i<N;i++){ if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",i+1);return 0;} }
 long long f=t.lo, e=t.hi; while(f<e && !t.c[f+t.off] && f<t.head) f++; while(e>f && !t.c[e+t.off] && e>t.head) e--;
 if(t.head<f) f=t.head; if(t.head>e) e=t.head;
 printf("SNAP %lld %lld %d ",N,t.head-f,st); for(long long x=f;x<=e;x++) putchar('0'+((x>=t.lo&&x<=t.hi)?t.c[x+t.off]:0)); printf("\n");}
