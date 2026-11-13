/* ticks MACHINE MAXSTEPS STATE W TEMPLATE...
   A tick configuration: head in STATE, the cells left of the head are  1 (0^(W-1) b)^L GAP  over blank tape, the
   cells from the head on are HEADER followed by pairs (x 1) (bit = 1 - x), then a tail.  TEMPLATE = name:GAP|HEADER.
   Prints one line per maximal run of consecutive ticks of one template in which U goes up by 1 (or overflows into
   L+1 digits) and V by a constant delta each tick:  "seg NAME n=... from STEP L U V tail -> STEP L U V tail  dV=..." */
#include "../../../tools/c/tm.h"
typedef unsigned __int128 u128;
static void p128(u128 v){char b[50];int i=49;b[i]=0;if(!v){putchar('0');return;}while(v){b[--i]='0'+(int)(v%10);v/=10;}fputs(b+i,stdout);}
typedef struct{char name[32];char gap[64];char hdr[256];int ng,nh;} tpl;
typedef struct{long long k;int t;int L;u128 U,V;int nb;char tail[200];int ok;} tick;
int W; tm_machine m;
static int dec(tm_tape*t,tpl*T,tick*o){
  long long h=t->head;
  for(int i=0;i<T->nh;i++) if(tm_get(t,h+i)!=T->hdr[i]-'0') return 0;
  for(int i=0;i<T->ng;i++) if(tm_get(t,h-T->ng+i)!=T->gap[i]-'0') return 0;
  long long p=h-T->ng-1; int L=0; u128 U=0,bit=1;
  while(1){
    if(p<t->lo-1) return 0;
    /* sentinel? cell p is 1 and everything left of it blank */
    if(tm_get(t,p)==1){ int blank=1; for(long long q=p-1;q>=t->lo;q--) if(tm_get(t,q)){blank=0;break;} if(blank) break; }
    /* block p-W+1..p : 0^(W-1) b */
    int b=tm_get(t,p); for(int i=1;i<W;i++) if(tm_get(t,p-i)) return 0;
    if(b) U|=bit; bit<<=1; L++; p-=W; if(L>120) return 0;
  }
  long long q=h+T->nh; u128 V=0; bit=1; int nb=0;
  while(tm_get(t,q+1)==1 && q+1<=t->hi){ if(tm_get(t,q)==0) V|=bit; bit<<=1; nb++; q+=2; if(nb>120) return 0;}
  int n=0; o->tail[0]=0;
  for(long long r=q;r<=t->hi && n<190;r++) o->tail[n++]='0'+tm_get(t,r); o->tail[n]=0;
  o->L=L;o->U=U;o->V=V;o->nb=nb;return 1;
}
static void pr(tick*a){printf("%lld L=%d U=",a->k,a->L);p128(a->U);printf(" V=");p128(a->V);printf(" nb=%d tail=%s",a->nb,a->tail);}
int main(int argc,char**argv){
  tm_parse(argv[1],&m); long long max=atoll(argv[2]); int S=argv[3][0]-'A'; W=atoi(argv[4]);
  int nt=argc-5; tpl T[8];
  for(int i=0;i<nt;i++){char*s=argv[5+i];char*c=strchr(s,':');char*b=strchr(s,'|');
    memcpy(T[i].name,s,c-s);T[i].name[c-s]=0; memcpy(T[i].gap,c+1,b-c-1);T[i].gap[b-c-1]=0; strcpy(T[i].hdr,b+1);
    T[i].ng=strlen(T[i].gap);T[i].nh=strlen(T[i].hdr);}
  tm_tape t; tm_tape_init(&t,1<<16); int st=0; long long k=0;
  tick first,prev,cur; int have=0,n=0; __int128 dV=0; long long total=0;
  while(k<max){
    if(st==S && tm_get(&t,t.head)==T[0].hdr[0]-'0'){
      for(int i=0;i<nt;i++){ if(dec(&t,&T[i],&cur)){ cur.k=k;cur.t=i; total++;
          int cont=0;
          if(have && prev.t==i){
            int okU=(cur.L==prev.L && cur.U==prev.U+1)||(cur.L==prev.L+1&&cur.U==0&&prev.U==(((u128)1)<<prev.L)-1);
            __int128 d=(__int128)cur.V-(__int128)prev.V;
            if(okU && (n==1 || d==dV)){cont=1; dV=d;}
          }
          if(cont){n++;prev=cur;}
          else{ if(have){printf("seg %s n=%d ",T[first.t].name,n);pr(&first);printf(" -> ");pr(&prev);printf(" dV=%lld\n",(long long)dV);}
                first=prev=cur;have=1;n=1;dV=0;}
          break;} }
    }
    k++; if(!tm_step(&m,&t,&st)){ if(have){printf("seg %s n=%d ",T[first.t].name,n);pr(&first);printf(" -> ");pr(&prev);printf(" dV=%lld\n",(long long)dV);} printf("HALT %lld\n",k); return 0;}
  }
  if(have){printf("seg %s n=%d ",T[first.t].name,n);pr(&first);printf(" -> ");pr(&prev);printf(" dV=%lld\n",(long long)dV);}
  printf("end %lld ticks %lld\n",k,total);
}
