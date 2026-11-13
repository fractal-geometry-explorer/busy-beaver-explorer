/* evw MACHINE STEPS STATE SIDE WORDS [FROM] [EVERY]
   At each event (head in STATE at the L or R end of the visited tape), print the tape as runs of the given words
   (comma separated, all rotations are NOT added; give them), greedy by longest total run, literals otherwise.
   Format: step  tokens ; the head shown as S> before its cell. Prints every EVERY-th event (default 1). */
#include "../../../tools/c/tm.h"
char W[16][16]; int WL[16], NW=0;
int main(int argc,char**argv){
  tm_machine m; tm_parse(argv[1],&m); long long N=atoll(argv[2]); int S=argv[3][0]-'A'; int side=argv[4][0]=='R';
  char buf[256]; strcpy(buf,argv[5]); for(char*p=strtok(buf,",");p;p=strtok(NULL,",")){strcpy(W[NW],p);WL[NW]=strlen(p);NW++;}
  long long from=argc>6?atoll(argv[6]):0, every=argc>7?atoll(argv[7]):1, cnt=0;
  tm_tape t; tm_tape_init(&t,1<<22); int st=0; long long k=0;
  long long maxev=-1;
  char*init=getenv("TAPE"); if(getenv("MAXEV")) maxev=atoll(getenv("MAXEV"));
  if(init){ /* tokens: digits strings, (w)^n, S> marks head before next cell */
    char b2[1<<16]; strncpy(b2,init,sizeof b2-1); long long p=0; int hs=-1; long long hp=0;
    for(char*tok=strtok(b2," ");tok;tok=strtok(NULL," ")){
      if(strlen(tok)>=2 && tok[1]=='>'){ hs=tok[0]-'A'; hp=p; tok+=2; if(!*tok) continue; }
      if(tok[0]=='('){ char w[64]; int wl=0; char*q=tok+1; while(*q!=')') w[wl++]=*q++; q+=2; long long n=atoll(q);
        for(long long i=0;i<n;i++) for(int j=0;j<wl;j++){ long long pos=p++; long long ii=pos+t.off; while(ii>=t.size){tm_grow(&t); ii=pos+t.off;} t.c[ii]=w[j]-'0'; } }
      else for(char*q=tok;*q;q++){ long long pos=p++; long long ii=pos+t.off; while(ii>=t.size){tm_grow(&t); ii=pos+t.off;} t.c[ii]=*q-'0'; }
    }
    t.lo=0; t.hi=p-1; t.head=hp; st=hs; }
  while(k<N){ if(!tm_step(&m,&t,&st)){printf("HALT %lld ",k); tm_print(&m,&t,st,stdout); return 0;} k++;
    if(st!=S) continue;
    if(side? t.head!=t.hi : t.head!=t.lo) continue;
    if(k<from) continue;
    if(maxev>=0 && cnt>=maxev) return 0;
    if((cnt++)%every) continue;
    printf("%lld",k);
    long long p=t.lo; char lit[64]; int nl=0;
    while(p<=t.hi){
      int best=-1; long long bn=0;
      for(int w=0;w<NW;w++){ long long n=0; for(;;){ int ok=1; for(int j=0;j<WL[w];j++){ long long q=p+n*WL[w]+j; if(q>t.hi||(q==t.head && !(n==0&&j==0))||tm_get(&t,q)!=W[w][j]-'0'){ok=0;break;} } if(!ok)break; n++; }
        if(n>=2 && n*WL[w]>bn*(best>=0?WL[best]:1)){best=w;bn=n;} }
      if(p==t.head){ if(nl){lit[nl]=0;printf(" %s",lit);nl=0;} printf(" %c>",'A'+st); }
      if(best>=0 && p!=t.head){ if(nl){lit[nl]=0;printf(" %s",lit);nl=0;} printf(" %s^%lld",W[best],bn); p+=bn*WL[best]; }
      else { if(p==t.head){printf("%d",tm_get(&t,p)); p++; continue;} lit[nl++]='0'+tm_get(&t,p); if(nl>60){lit[nl]=0;printf(" %s",lit);nl=0;} p++; }
    }
    if(nl){lit[nl]=0;printf(" %s",lit);}
    printf("\n");
  }
  return 0;}
