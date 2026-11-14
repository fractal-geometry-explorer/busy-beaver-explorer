#include "../../../tools/c/tm.h"
// print "visit step ones" at each step after which the head is on a never-visited cell to the right and state==A
int main(int argc,char**argv){ tm_machine m; tm_parse(argv[1],&m); long long nv=atoll(argv[2]);
  tm_tape t; tm_tape_init(&t,1<<24); int st=0; long long k=0,v=0,mx=0,ones=0;
  while(v<nv){ long long p=t.head; int old=tm_get(&t,p); if(!tm_step(&m,&t,&st)){printf("halt %lld\n",k+1);return 0;} k++;
    ones+= tm_get(&t,p)-old;
    if(t.head>mx){ mx=t.head; if(st==0){ v++; printf("%lld %lld %lld\n",v,k,ones);} } }
  return 0;}
