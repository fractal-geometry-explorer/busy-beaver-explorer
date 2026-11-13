/* st MACHINE STEPS ROWS OUT.pgm [mode]: space-time diagram. mode 0: rows at equal step spacing;
   mode 1: one row each time the head reaches its rightmost visited cell (subsampled to ROWS) */
#include "../../../tools/c/tm.h"
int main(int argc,char**argv){
  tm_machine m; tm_parse(argv[1],&m); long long N=atoll(argv[2]); int R=atoi(argv[3]);
  tm_tape t; tm_tape_init(&t,1<<20); int st=0;
  /* first pass: find extent */
  { tm_tape u; tm_tape_init(&u,1<<20); int s2=0,h; tm_run(&m,&u,&s2,N,&h); t.lo=u.lo; t.hi=u.hi; tm_tape_free(&u);}
  long long lo=t.lo,hi=t.hi,W=hi-lo+1; t.lo=t.hi=0;
  FILE*f=fopen(argv[4],"wb"); fprintf(f,"P5 %lld %d 255\n",W,R);
  unsigned char*row=malloc(W);
  for(int r=0;r<R;r++){ long long target=N*(r+1)/R; static long long k=0;
    while(k<target){ if(!tm_step(&m,&t,&st)) break; k++; }
    for(long long p=lo;p<=hi;p++) row[p-lo]= tm_get(&t,p)?0:255;
    long long hp=t.head-lo; if(hp>=0&&hp<W) row[hp]=128;
    fwrite(row,1,W,f);}
  fclose(f); return 0;}
