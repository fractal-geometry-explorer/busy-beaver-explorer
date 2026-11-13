#include "../../../tools/c/tm.h"
/* chg MACHINE FROM TO POS STATE: at each turn at POS(rel lo at FROM) in STATE, compare tape with previous snapshot; count changes per cell (rel engine) */
int main(int argc,char**argv){tm_machine m; tm_parse(argv[1],&m); long long from=atoll(argv[2]), to=atoll(argv[3]); long long pos=atoll(argv[4]); int S=argv[5][0]-'A';
 tm_tape t; tm_tape_init(&t,1<<20); int st=0; long long k=0; int ld=0; long long base=0; int set=0; static unsigned char prev[4096]; static long long ch[4096]; int havep=0; long long nsnap=0; long long E=0;
 while(k<to){ long long h0=t.head; k++; if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);break;}
  int d=t.head>h0?1:-1;
  if(k>=from){ if(!set){base=t.lo;set=1;} if(d!=ld && t.head-base==pos && st==S){ nsnap++; E=t.head; for(int i=0;i<4096;i++){ int v=tm_get(&t,t.head-2048+i); if(havep && v!=prev[i]) ch[i]++; prev[i]=v;} havep=1; } }
  ld=d; }
 printf("snaps %lld\n",nsnap);
 for(int i=0;i<4096;i++) if(t.head-2048+i>=t.lo && E-2048+i<=t.hi) { }
 /* print last snapshot with change counts as log2 digit */
 int W0=argc>6?atoi(argv[6]):200, W1=argc>7?atoi(argv[7]):300; for(int i=2048-W0;i<2048+W1;i++){ long long p=E-2048+i; if(p<t.lo||p>t.hi) continue; int c=0; long long x=ch[i]; while(x){c++;x>>=1;} if(ch[i]==0) putchar('0'+prev[i]); else putchar(c<10?'a'+c-1:'A'+c-10); }
 putchar('\n');
}
