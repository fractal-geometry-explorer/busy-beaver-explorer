/* sstat MACHINE STEPS : for the state S of the halting transition, count how often S is entered, what it reads, and
 * where (distance of the head from the nearer end of the visited tape, 0..6 and 7 for "7 or more").
 * gcc -O2 -I tools/c -o sstat holdouts/MACHINE/c/sstat.c   (from the repo root; tm.h is in tools/c) */
#include "tm.h"
int main(int c,char**v){tm_machine m;tm_parse(v[1],&m);long long mx=atoll(v[2]);
int hs=-1,hb=-1; const char*t=v[1];for(int s=0;s<6;s++)for(int b=0;b<2;b++)if(t[7*s+3*b]=='-'){hs=s;hb=b;}
tm_tape tp;tm_tape_init(&tp,1<<16);int st=0;long long cnt[2]={0,0};long long dl[2][8]={{0}},dr[2][8]={{0}};
for(long long k=0;k<mx;k++){ if(!tm_step(&m,&tp,&st)){printf("halted %lld\n",k+1);return 0;}
 if(st==hs){int b=tm_get(&tp,tp.head);cnt[b]++;long long a=tp.head-tp.lo,bb=tp.hi-tp.head;
  int ia=a<7?a:7, ib=bb<7?bb:7; dl[b][ia]++; dr[b][ib]++;}}
printf("state %c (halts on %d): reads0 %lld reads1 %lld\n",'A'+hs,hb,cnt[0],cnt[1]);
for(int b=0;b<2;b++){printf(" read %d dist-from-left:",b);for(int i=0;i<8;i++)printf(" %lld",dl[b][i]);printf("  dist-from-right:");for(int i=0;i<8;i++)printf(" %lld",dr[b][i]);printf("\n");}}
