#include "../../../tools/c/tm.h"
int main(int argc,char**argv){tm_machine m; tm_parse(argv[1],&m); long long N=atoll(argv[2]);
 tm_tape t; tm_tape_init(&t,1<<16); int st=0; long long cnt[8][2]={{0}};
 for(long long k=0;k<N;k++){ int y=tm_get(&t,t.head); cnt[st][y]++; if(!tm_step(&m,&t,&st)){printf("halted at %lld\n",k+1);break;} }
 for(int s=0;s<m.n;s++) printf("%c: %12lld %12lld\n",'A'+s,cnt[s][0],cnt[s][1]); }
