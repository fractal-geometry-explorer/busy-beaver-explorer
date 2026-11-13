/* rle_test: the accelerated simulator of rle.h against tools/c/tm.h: state and head position after every move, and
 * 3,000 cells on each side of the head every 1,000 moves.  usage: rle_test MACHINE MOVES */
/* compare rle against tm.h direct simulation: same tape after N moves */
#include "rle.h"
#include "../../../tools/c/tm.h"
int main(int argc,char**argv){ tm t; init(&t,argv[1]); ll N=atoll(argv[2]);
  tm_machine m; tm_parse(argv[1],&m); tm_tape tp; tm_tape_init(&tp,1<<20); int st=0; ll k=0; int bad=0;
  for(ll i=0;i<N && !t.halted;i++){ move(&t);
    while(k<t.steps && !t.halted){ k++; if(!tm_step(&m,&tp,&st)) { break;} }
    if(t.halted) break;
    if(st!=t.st || tp.head!=t.pos){ printf("state/pos mismatch at move %lld step %lld\n",i,t.steps); bad=1; break; }
    /* compare a window */
    if(i%1000==0){ ll p=t.pos; /* reconstruct around head */
      ll q=p; for(ll r=t.R.n-1;r>=0;r--){ for(ll c=0;c<t.R.a[r].len && q<p+3000;c++,q++) if(tm_get(&tp,q)!=t.R.a[r].sym){printf("R mismatch move %lld\n",i);bad=1;break;} if(bad||q>=p+3000)break;}
      q=p-1; for(ll r=t.L.n-1;r>=0 && !bad;r--){ for(ll c=0;c<t.L.a[r].len && q>p-3000;c++,q--) if(tm_get(&tp,q)!=t.L.a[r].sym){printf("L mismatch move %lld\n",i);bad=1;break;} if(q<=p-3000)break;}
      if(bad) break; }
  }
  printf("%s: %lld steps, halted %d\n", bad?"MISMATCH":"agree", t.steps, t.halted); return bad; }
