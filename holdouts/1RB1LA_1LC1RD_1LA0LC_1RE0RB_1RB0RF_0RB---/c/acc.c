/* acc MACHINE MAXSTEPS SKIP K EXCL < tape
   Direct simulation from a run-length tape.  At each pass start (state A on 0) every candidate even-config pattern
   (o,p,c): top block odd >= 1+2o; right: 1^m, p frozen gaps W (each followed by a single 1), (c+1) gaps 0^2 (single 1s)
   is counted under its key (o,p,c,m,W).  When a key (not in EXCL, a comma list of key strings) reaches K/2 counts,
   the next K detections of that key are printed with their tapes.
   Output: "det STEP KEY" + tape lines, or "halt STEP", or "limit STEP" + tape. */
#include "../../../tools/c/tm.h"
static char buf[1<<27];
static void dump(tm_tape *t,int st){
  long long p=t->lo; 
  while(p<=t->hi){ if(p==t->head){ printf(" %c>%d",'A'+st,tm_get(t,p)); p++; continue;}
    int v=tm_get(t,p); long long q=p; while(q<=t->hi&&q!=t->head&&tm_get(t,q)==v) q++;
    if(q-p>1) printf(" %d^%lld",v,q-p); else printf(" %d",v); p=q; }
  printf("\n");
}
#define NK 8192
typedef struct { char key[96]; long long cnt; } ent;
static ent tab[NK]; static int ntab=0;
static int find(const char*k){ for(int i=0;i<ntab;i++) if(!strcmp(tab[i].key,k)) return i; if(ntab<NK){ strcpy(tab[ntab].key,k); tab[ntab].cnt=0; return ntab++; } return -1; }
static int G[16]; static int nG; static int GB=2;
static int keys(tm_tape *t, char out[][96]){
  long long q=t->head+1; int m=0; while(tm_get(t,q)==1){m++;q++;}
  if(m==0) return 0;
  nG=0; while(nG<16){ int z=0; while(z<1000000&&q<=t->hi&&tm_get(t,q)==0){z++;q++;} if(q>t->hi||z==0) break; if(tm_get(t,q)!=1||tm_get(t,q+1)!=0) { G[nG++]=-z; break;} G[nG++]=z; q++; }
  long long l=t->head-1; int b=0; while(l>=t->lo&&tm_get(t,l)==1){b++;l--;}
  if(b%2==0) return 0;
  int n=0;
  for(int o=0;o<=3;o++){ if(b<1+2*o) break;
    for(int p=0;p<=3;p++) for(int c=0;c<=6;c++){
      if(p+c+1>nG) continue; int ok=1;
      for(int i=0;i<p;i++) if(G[i]<0) ok=0;
      for(int i=p;i<=p+c;i++) if(G[i]!=GB) ok=0;
      if(!ok) continue;
      char *s=out[n++]; int w=sprintf(s,"%d.%d.%d.%d",o,p,c,m); for(int i=0;i<p;i++) w+=sprintf(s+w,".%d",G[i]);
      if(n>=200) return n; } }
  return n;
}
int main(int argc,char**argv){
  tm_machine m; tm_parse(argv[1],&m); if(getenv("GB")) GB=atoi(getenv("GB")); long long max=atoll(argv[2]); long long skip=atoll(argv[3]); int K=atoi(argv[4]);
  const char *excl=argc>5?argv[5]:"";
  size_t n=fread(buf,1,sizeof buf-1,stdin); buf[n]=0;
  tm_tape t; tm_tape_init(&t,1<<22); int st=0; long long pos=0, headpos=0;
  char *p=strtok(buf," \n\t");
  while(p){
    if(strchr(p,'>')){ st=p[0]-'A'; int b=p[2]-'0'; long long i=pos+t.off; while(i>=t.size){tm_grow(&t); i=pos+t.off;} t.c[i]=b; headpos=pos; pos++; }
    else { int b=p[0]-'0'; long long r=1; char*c=strchr(p,'^'); if(c) r=atoll(c+1); for(long long k=0;k<r;k++){ long long i=pos+t.off; while(i>=t.size){tm_grow(&t); i=pos+t.off;} t.c[i]=b; pos++; } }
    p=strtok(NULL," \n\t");
  }
  t.head=headpos; t.lo=0; t.hi=pos-1;
  static char ks[200][96]; char target[96]=""; int got=0; long long lastdet=0;
  for(long long k=0;k<max;k++){
    if(st==0&&tm_get(&t,t.head)==0&&k>skip){
      if(target[0] && k-lastdet>5000000){ printf("reset\n"); int e=find(target); if(e>=0) tab[e].cnt=-1000000; target[0]=0; got=0; }
      int nk=keys(&t,ks);
      for(int i=0;i<nk;i++){
        if(target[0]){ if(!strcmp(ks[i],target)){ printf("det %lld %s\n",k,target); dump(&t,st); lastdet=k; if(++got>=K) return 0; } continue; }
        char pat[100]; sprintf(pat,",%s,",ks[i]); if(strstr(excl,pat)) continue;
        int e=find(ks[i]); if(e<0) continue;
        if(++tab[e].cnt>=K/2){ strcpy(target,ks[i]); printf("det %lld %s\n",k,target); dump(&t,st); got=1; lastdet=k; break; }
      }
    }
    if(!tm_step(&m,&t,&st)){printf("halt %lld\n",k+1);return 0;}
  }
  printf("limit %lld\n",max); dump(&t,st);
  return 0;
}
