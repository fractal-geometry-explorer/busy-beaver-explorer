/* sstate MACHINE MAX TAPE NEV: run from TAPE (string of 0/1, head before the cell marked by "X>" letter state)
   and at every event (head in state B at the left end) print: step v0 nruns [runs if nruns<=60]  (NEV events max) */
#include "../../../tools/c/tm.h"
int main(int argc,char**argv){
  tm_machine m; tm_parse(argv[1],&m); long long max=atoll(argv[2]); const char*tp=argv[3]; long long nev=atoll(argv[4]);
  int ast=argc>5?argv[5][0]-'A':1;
  tm_tape t; tm_tape_init(&t,1<<22); int st=0; long long k=0;
  long long pos=0; for(const char*c=tp;*c;c++){ if(*c=='>')continue; if(c[1]=='>'){st=*c-'A'; t.head=pos; continue;} if(*c=='0'||*c=='1'){ t.c[pos+t.off]=*c-'0'; pos++;} }
  t.lo=0; t.hi=pos-1; static long long buf[100];
  while(k<max){ k++; if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);return 0;}
    if(st==ast && t.head==t.lo){
      int n=0; long long p=t.lo; int v0=tm_get(&t,p);
      while(p<=t.hi){int v=tm_get(&t,p); long long q=p; while(q<=t.hi&&tm_get(&t,q)==v)q++; if(n<100)buf[n]=q-p; n++; p=q;}
      printf("%lld %d %d",k,v0,n); if(n<=60) for(int i=0;i<n;i++)printf(" %lld",buf[i]); printf("\n");
      if(--nev<=0) return 0;
    }}
  printf("END %lld\n",k); return 0;}
