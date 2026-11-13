/* pat MACHINE MAXSTEPS STATE LEFT|RIGHT [START [EVERY [MAXLINES]]]
   print "STEP tape" whenever the head is in STATE and the cells match: LEFT are the cells just left of the head
   (nearest last), RIGHT starts with the head cell. '.' matches anything. */
#include "../../../tools/c/tm.h"
int main(int argc,char**argv){
  tm_machine m; if(tm_parse(argv[1],&m)) return 1;
  long long max=atoll(argv[2]); int S=argv[3][0]-'A';
  char *pat=argv[4]; char *bar=strchr(pat,'|'); int nl=bar-pat; char *R=bar+1; int nr=strlen(R);
  long long start=argc>5?atoll(argv[5]):0, every=argc>6?atoll(argv[6]):1, maxl=argc>7?atoll(argv[7]):1000000000LL;
  tm_tape t; tm_tape_init(&t,1<<16); int st=0; long long k=0,cnt=0,lines=0;
  while(k<max){
    if(st==S && k>=start){
      int ok=1;
      for(int i=0;i<nl&&ok;i++){char c=pat[i]; if(c=='.')continue; if(tm_get(&t,t.head-nl+i)!=c-'0')ok=0;}
      for(int i=0;i<nr&&ok;i++){char c=R[i]; if(c=='.')continue; if(tm_get(&t,t.head+i)!=c-'0')ok=0;}
      if(ok){ if(cnt%every==0){printf("%lld ",k); tm_print(&m,&t,st,stdout); if(++lines>=maxl)break;} cnt++; }
    }
    k++; if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);return 0;}
  }
  fprintf(stderr,"matches %lld steps %lld\n",cnt,k);
}
