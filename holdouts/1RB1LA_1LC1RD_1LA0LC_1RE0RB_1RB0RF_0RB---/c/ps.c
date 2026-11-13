/* ps MACHINE MAXSTEPS T < tape : direct simulation from a run-length tape; stops at the first pass start (A on 0)
   in a regular counter configuration with E bit-length >= T and F jump capacity >= T bits.
   Output: "det STEP" + tape | "halt STEP" | "limit STEP" + tape.  GB/GP env: base gap and period (2/3 or 4/5). */
#include "../../../tools/c/tm.h"
static char buf[1<<28];
static void dump(tm_tape *t,int st){
  long long p=t->lo;
  while(p<=t->hi){ if(p==t->head){ printf(" %c>%d",'A'+st,tm_get(t,p)); p++; continue;}
    int v=tm_get(t,p); long long q=p; while(q<=t->hi&&q!=t->head&&tm_get(t,q)==v) q++;
    if(q-p>1) printf(" %d^%lld",v,q-p); else printf(" %d",v); p=q; }
  printf("\n");
}
static int GB=2,GP=3;
static int check(tm_tape *t,int T){
  long long q=t->head+1; int m=0; while(tm_get(t,q)==1){m++;q++;}
  if(m!=3&&m!=5) return 0;
  long long l=t->head-1; long long eb=0;
  while(eb<T){ int b=0; while(l>=t->lo&&tm_get(t,l)==1){b++;l--;} if(b==0) break;
    if(b%2==0) break;
    eb+=(b-1)/2+1;
    if(tm_get(t,l)!=0) break; l--; if(tm_get(t,l)!=1) break; }
  if(eb<T) return 0;
  long long P=-1, hz=-1;   /* P: position of last 1 bit; hz: highest zero bit */
  while(hz+1<T){ long long z2=0; while(q<=t->hi&&tm_get(t,q)==0){z2++;q++;} if(q>t->hi) break;
    int c2=0; while(tm_get(t,q)==1){c2++;q++;}
    if(c2!=1||z2<GB||(z2-GB)%GP!=0) break;
    long long d=(z2-GB)/GP; if(d>0) hz=P+d; P=P+d+1; }
  return hz+1>=T;
}

static long long mon_n=0, mon_maxdef=0, mon_maxb2=0, mon_p1=0, mon_maxeven=0, mon_p1first=-1;
static void monitor(tm_tape *t,long long k){
  /* right side: skip the top block; then gaps and blocks */
  long long q=t->head+1; while(tm_get(t,q)==1) q++;
  int first=1; long long def=0,b2=0,p1=0;
  while(q<=t->hi){ long long z=0; while(q<=t->hi&&tm_get(t,q)==0){z++;q++;} if(q>t->hi) break;
    long long c=0; while(tm_get(t,q)==1){c++;q++;}
    if(!first){ if(z%GP!=GB%GP) def++; }
    if(c>=2) b2++;
    if(z%GP==(GB+GP-1)%GP && c>=2) p1++;
    first=0; }
  long long l=t->head-1; long long ev=0; int nb=0;
  while(l>=t->lo){ long long c=0; while(l>=t->lo&&tm_get(t,l)==1){c++;l--;} if(c>0&&c%2==0) ev++; nb++; while(l>=t->lo&&tm_get(t,l)==0) l--; }
  mon_n++; if(def>mon_maxdef) mon_maxdef=def; if(b2>mon_maxb2) mon_maxb2=b2; if(ev>mon_maxeven) mon_maxeven=ev;
  if(p1){ mon_p1++; if(mon_p1first<0) mon_p1first=k; }
}
static void monprint(void){ if(getenv("MON")) printf("mon %lld %lld %lld %lld %lld %lld\n",mon_n,mon_maxdef,mon_maxb2,mon_maxeven,mon_p1,mon_p1first); }
int main(int argc,char**argv){
  tm_machine m; tm_parse(argv[1],&m); if(getenv("GB")) GB=atoi(getenv("GB")); if(getenv("GP")) GP=atoi(getenv("GP"));
  long long max=atoll(argv[2]); int domon=getenv("MON")!=NULL; int T=atoi(argv[3]);
  size_t n=fread(buf,1,sizeof buf-1,stdin); buf[n]=0;
  tm_tape t; tm_tape_init(&t,1<<22); int st=0; long long pos=0, headpos=0;
  char *p=strtok(buf," \n\t");
  while(p){
    if(strchr(p,'>')){ st=p[0]-'A'; int b=p[2]-'0'; long long i=pos+t.off; while(i>=t.size){tm_grow(&t); i=pos+t.off;} t.c[i]=b; headpos=pos; pos++; }
    else { int b=p[0]-'0'; long long r=1; char*c=strchr(p,'^'); if(c) r=atoll(c+1); for(long long k=0;k<r;k++){ long long i=pos+t.off; while(i>=t.size){tm_grow(&t); i=pos+t.off;} t.c[i]=b; pos++; } }
    p=strtok(NULL," \n\t");
  }
  t.head=headpos; t.lo=0; t.hi=pos-1;
  for(long long k=0;k<max;k++){
    if(st==0&&tm_get(&t,t.head)==0){ if(domon) monitor(&t,k); if(k>0&&check(&t,T)){ printf("det %lld\n",k); dump(&t,st); monprint(); return 0; } }
    if(!tm_step(&m,&t,&st)){printf("halt %lld\n",k+1);monprint();return 0;}
  }
  printf("limit %lld\n",max); dump(&t,st); monprint();
  return 0;
}
