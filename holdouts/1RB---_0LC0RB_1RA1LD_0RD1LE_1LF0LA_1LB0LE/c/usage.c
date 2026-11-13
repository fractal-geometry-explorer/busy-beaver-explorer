#include "../../../tools/c/tm.h"
/* usage MACHINE N: count of each transition, and for each transition the counts of (next read symbol) */
int main(int argc,char**argv){tm_machine m; tm_parse(argv[1],&m); long long n=atoll(argv[2]);
 tm_tape t; tm_tape_init(&t,1<<20); int st=0; long long cnt[10][2]={0}, nx[10][2][2]={0}; int ps=-1,py=0;
 for(long long k=0;k<n;k++){ int y=tm_get(&t,t.head); if(ps>=0) nx[ps][py][y]++; cnt[st][y]++; ps=st; py=y; if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k+1);break;} }
 for(int s=0;s<m.n;s++) for(int y=0;y<2;y++) printf("%c%d: %lld (next reads 0:%lld 1:%lld)\n",'A'+s,y,cnt[s][y],nx[s][y][0],nx[s][y][1]);
}
