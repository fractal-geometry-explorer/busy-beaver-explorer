/* each time head reaches hi (right end) after having been at least D cells left of it: print step, hi, lo, state, cells added since last visit */
#include "../../../tools/c/tm.h"
int main(int argc,char**argv){
  tm_machine m; tm_parse(argv[1],&m); long long max=atoll(argv[2]); long long D=atoll(argv[3]);
  tm_tape t; tm_tape_init(&t,1<<16); int st=0; long long k=0; int away=1; long long lasthi=0, lastk=0, minpos=0;
  while(k<max){ k++;
    if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);break;}
    if(t.head < t.hi-D) { away=1; }
    if(t.head<minpos) minpos=t.head;
    if(away && t.head>=t.hi-1){ printf("%lld %lld %lld %c %lld %lld minpos %lld\n",k,t.hi,t.lo,'A'+st,t.hi-lasthi,k-lastk,minpos); lasthi=t.hi; lastk=k; away=0; minpos=t.head; }
  }
}
