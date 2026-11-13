/* evrun MACHINE MAX rec L|R K  |  evrun MACHINE MAX at S L|R K   (S may be '*')
   prints: STEPS STATE runs, where runs = 1-run lengths separated by single 0s, zK for K>=2 zeros, '|S>' at head */
#include "../../../tools/c/tm.h"
static char last[64]; static long long cnt; static int first;
static void emit(FILE*f,const char*tok){ if(cnt&&!strcmp(tok,last)){cnt++;return;} if(cnt){fprintf(f,cnt>1?" %s^%lld":" %s",last,cnt);} strcpy(last,tok);cnt=1;}
static void flush(FILE*f){ if(cnt) fprintf(f,cnt>1?" %s^%lld":" %s",last,cnt); cnt=0; last[0]=0;}
static void pr(const tm_tape*t,int st,FILE*f){
  long long p=t->lo; char buf[64];
  while(p<=t->hi && p<t->head && tm_get(t,p)==0) p++;
  long long hi=t->hi; while(hi>t->head && tm_get(t,hi)==0) hi--;
  cnt=0;
  while(p<=hi){
    if(p==t->head){ flush(f); fprintf(f," |%c>%d",'A'+st,tm_get(t,p)); p++; continue;}
    int v=tm_get(t,p); long long q=p; while(q<=hi&&q!=t->head&&tm_get(t,q)==v)q++;
    if(v==1){sprintf(buf,"%lld",q-p);emit(f,buf);}
    else if(q-p>1 || q==t->head || p==t->head+1 ){ if(q-p>1){sprintf(buf,"z%lld",q-p);emit(f,buf);} else {emit(f,"z1");} }
    p=q;
  }
  flush(f); fputc('\n',f);
}
int main(int argc,char**argv){
  tm_machine m; tm_parse(argv[1],&m); long long max=atoll(argv[2]); int mode=!strcmp(argv[3],"rec")?1:2;
  int S=-1,side; long long K;
  if(mode==1){side=argv[4][0]=='R';K=atoll(argv[5]);} else {S=argv[4][0]=='*'?-1:argv[4][0]-'A';side=argv[5][0]=='R';K=atoll(argv[6]);}
  long long every=argc>7?atoll(argv[7]):1; long long seen=0;
  tm_tape t; tm_tape_init(&t,1<<16); int st=0; long long k=0,lines=0;
  while(k<max){ long long lo=t.lo,hi=t.hi; k++; if(!tm_step(&m,&t,&st)){printf("HALT %lld\n",k);return 0;}
    int ev=0;
    if(mode==1) ev= side? t.hi>hi : t.lo<lo;
    else ev=(S<0||st==S)&&t.head==(side?t.hi:t.lo);
    if(ev){ seen++; if(seen%every==0 && lines<K){printf("%lld %c",k,'A'+st);pr(&t,st,stdout);lines++;} }
  }
  printf("running %lld\n",k); return 0;}
