// near MACHINE STEPS: how close the run comes to a halt of 1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF.  A halt needs F reading 0
// or B reading 1 with the cells 0, 1, 0 on its left (lean/Halt.lean); this counts F0 and B1 by their three left cells.
#include "../../../tools/c/tm.h"
int main(int argc,char**argv){
  tm_machine m; tm_parse(argv[1],&m); long long max=atoll(argv[2]);
  tm_tape t; tm_tape_init(&t,1<<16); int st=0; long long cnt[2][8]={0}; long long last[2][8];
  for(long long k=0;k<max;k++){ int y=tm_get(&t,t.head);
    if((st==5&&y==0)||(st==1&&y==1)){ int w=tm_get(&t,t.head-1)|tm_get(&t,t.head-2)<<1|tm_get(&t,t.head-3)<<2; int i=st==5?0:1; cnt[i][w]++; last[i][w]=k; }
    if(!tm_step(&m,&t,&st)){printf("halt %lld\n",k+1);break;} }
  for(int i=0;i<2;i++)for(int w=0;w<8;w++) printf("%s l0l1l2=%d%d%d %lld last %lld\n",i?"B1":"F0",w&1,(w>>1)&1,(w>>2)&1,cnt[i][w],cnt[i][w]?last[i][w]:-1);
}
