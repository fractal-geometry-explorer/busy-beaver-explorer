/* zrec M N STATE WORD [PRINT]: each time STATE reads a fresh cell at the left end, strip leading copies of WORD from
   the tape right of the head and print: step, copies K, length of the rest Z, hash of Z (and Z if PRINT). */
#include "../../../tools/c/tm.h"
int main(int argc,char**argv){tm_machine m; tm_parse(argv[1],&m); long long N=atoll(argv[2]); int S=argv[3][0]-'A';
 const char*W=argv[4]; int wl=strlen(W); int pr=argc>5?atoi(argv[5]):0;
 tm_tape t; tm_tape_init(&t,1<<16); int st=0; long long lo0=1;
 for(long long k=0;k<N;k++){
  if(st==S && t.head<lo0 ){ lo0=t.head;
   long long p=t.head+1,K=0; while(p+wl-1<=t.hi){int ok=1; for(int j=0;j<wl;j++) if(tm_get(&t,p+j)!=W[j]-'0'){ok=0;break;} if(!ok)break; K++; p+=wl;}
   unsigned long long h=1469598103934665603ULL; for(long long q=p;q<=t.hi;q++){h^=tm_get(&t,q)+1;h*=1099511628211ULL;}
   printf("%lld %lld %lld %016llx",k,K,t.hi-p+1,h); if(pr){putchar(' ');for(long long q=p;q<=t.hi;q++)putchar('0'+tm_get(&t,q));} putchar('\n'); }
  if(!tm_step(&m,&t,&st)){printf("halted at %lld\n",k+1);break;} }
}
