/* ctx MACHINE STEPS [S y PRINTK]: count (state,read,right-neighbour) triples; print tape at first PRINTK events of state S reading y */
#include "../../../tools/c/tm.h"
int main(int argc,char**argv){
  tm_machine m; tm_parse(argv[1],&m); long long max=atoll(argv[2]);
  int ps=-1,py=-1; long long pk=0; if(argc>5){ps=argv[3][0]-'A';py=atoi(argv[4]);pk=atoll(argv[5]);}
  tm_tape t; tm_tape_init(&t,1<<16); int st=0; long long cnt[10][2][4]={0}; long long first[10][2][4]; memset(first,-1,sizeof first);
  long long k=0,printed=0;
  for(k=0;k<max;k++){
    int y=tm_get(&t,t.head), r=tm_get(&t,t.head+1), l=tm_get(&t,t.head-1);
    int c=r*2+l; cnt[st][y][c]++; if(first[st][y][c]<0) first[st][y][c]=k;
    if(st==ps&&y==py&&printed<pk){printf("%lld ",k);tm_print(&m,&t,st,stdout);printed++;}
    if(!tm_step(&m,&t,&st)){printf("halted %lld\n",k+1);break;}
  }
  for(int s=0;s<m.n;s++)for(int y=0;y<2;y++)for(int c=0;c<4;c++) if(cnt[s][y][c]) printf("%c%d l=%d r=%d : %lld first %lld\n",'A'+s,y,c&1,c>>1,cnt[s][y][c],first[s][y][c]);
}
