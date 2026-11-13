#include "../../../tools/c/tm.h"
int main(int argc,char**argv){tm_machine m; tm_parse(argv[1],&m); long long n=atoll(argv[2]);
 tm_tape t; tm_tape_init(&t,1<<16); int st=0; int h=0; long long k=tm_run(&m,&t,&st,n,&h);
 printf("%s %s %lld width %lld left %lld right %lld ones %lld\n",argv[1],h?"HALT":"running",k,t.hi-t.lo+1,-t.lo,t.hi,tm_ones(&t)); }
