/* frun MACHINE MAX TAPEFILE rec R|L K   : start from config in TAPEFILE: line1 "state headindex", line2 bits; same output as evrun */
#include "../../../tools/c/tm.h"
static char last[64]; static long long cnt;
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
    else if(q-p>1){sprintf(buf,"z%lld",q-p);emit(f,buf);} else if(q==t->head||p==t->head+1) emit(f,"z1");
    p=q;
  }
  flush(f); fputc('\n',f);
}
static char tb[1<<24];
int main(int argc,char**argv){
  tm_machine m; tm_parse(argv[1],&m); long long max=atoll(argv[2]);
  FILE*fi=fopen(argv[3],"r"); char sc; long long hidx; fscanf(fi," %c %lld %s",&sc,&hidx,tb); fclose(fi);
  tm_tape t; tm_tape_init(&t,1<<26); long long n=strlen(tb);
  for(long long i=0;i<n;i++) t.c[t.off+i]=tb[i]-'0'; t.lo=0; t.hi=n-1; t.head=hidx; int st=sc-'A';
  int mode=!strcmp(argv[4],"rec")?1:2; int S=-1,side; long long K;
  if(mode==1){side=argv[5][0]=='R';K=atoll(argv[6]);} else {S=argv[5][0]=='*'?-1:argv[5][0]-'A';side=argv[6][0]=='R';K=atoll(argv[7]);}
  long long k=0,lines=0;
  while(k<max){ long long lo=t.lo,hi=t.hi; k++; if(!tm_step(&m,&t,&st)){printf("HALT %lld ",k);pr(&t,st,stdout);return 0;}
    int ev; if(mode==1) ev= side? t.hi>hi : t.lo<lo; else ev=(S<0||st==S)&&t.head==(side?t.hi:t.lo);
    if(ev && lines<K){printf("%lld %c",k,'A'+st);pr(&t,st,stdout);lines++;}
  }
  printf("running %lld\n",k); return 0;}
