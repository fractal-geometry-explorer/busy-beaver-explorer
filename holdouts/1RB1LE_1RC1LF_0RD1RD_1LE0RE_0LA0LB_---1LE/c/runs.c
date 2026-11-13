/* runs: the block structure of the tape at each visit of one end of the tape.
   build: gcc -O2 -o runs runs.c;  example: ./runs 1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE 20000000000 E R 60 */
/* runs MACHINE MAX STATE L|R MAXRUNS [K]: at each event (head in STATE at the L/R end of visited tape),
   print "step runs..." where runs are RLE lengths of the tape from lo to hi, first run tagged with its symbol. */
#include "../../../tools/c/tm.h"
int main(int argc,char**argv){
  tm_machine m; tm_parse(argv[1],&m); long long max=atoll(argv[2]); int ast=argv[3][0]-'A', side=argv[4][0]=='R';
  int maxr=atoi(argv[5]); long long K=argc>6?atoll(argv[6]):1LL<<60, lines=0;
  tm_tape t; tm_tape_init(&t,1<<20); int st=0; long long k=0;
  long long *buf=malloc(sizeof(long long)*(maxr+2));
  while(k<max){ k++; if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);return 0;}
    if(st==ast && t.head==(side?t.hi:t.lo)){
      int n=0; long long p=t.lo; int v0=tm_get(&t,p);
      while(p<=t.hi && n<=maxr){int v=tm_get(&t,p); long long q=p; while(q<=t.hi&&tm_get(&t,q)==v)q++; buf[n++]=q-p; p=q;}
      if(n<=maxr){ printf("%lld %d:",k,v0); for(int i=0;i<n;i++)printf(" %lld",buf[i]); printf("\n"); if(++lines>=K)break;}
    }}
  printf("END %lld\n",k); return 0;}
