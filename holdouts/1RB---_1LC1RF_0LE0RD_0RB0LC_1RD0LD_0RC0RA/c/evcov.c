// evcov M STEPS P S RULES [K] [FROM]: at every event (head on cell P in state S, cells counted from the start cell),
// match the tape against each rule of RULES (lines "name LEFTREGEX RIGHTREGEX"; LEFTREGEX is the word just left of
// the head written left to right, RIGHTREGEX starts at the head cell; ERE over 0/1 with groups, '$' = end of the
// visited tape). WATCH S:w (or S:<w, w starting one cell left of the head) reports each time state S has w there. Counts per rule; prints the first K unmatched events (count step lo tape-with-|) and a summary.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <regex.h>
#define N (1<<22)
unsigned char tape[N];
static char lbuf[N], rbuf[N];
// reverse a regex of the grammar: atom := 0|1|'('seq')' quant? ; quant := * + ? {..}; also '$' at end -> '$' stays at end
static void rev(const char*s,int a,int b,char*out,int*o){ // reverse s[a..b)
  // split into atoms
  int st[512][2],na=0,i=a;
  while(i<b){int j=i; if(s[i]=='('){int d=0; do{if(s[j]=='(')d++; if(s[j]==')')d--; j++;}while(d); } else j=i+1;
    while(j<b&&(s[j]=='*'||s[j]=='+'||s[j]=='?')) j++;
    if(j<b&&s[j]=='{'){while(s[j]!='}')j++; j++;}
    st[na][0]=i; st[na][1]=j; na++; i=j;}
  for(int k=na-1;k>=0;k--){int x=st[k][0],y=st[k][1];
    if(s[x]=='('){int d=0,j=x; do{if(s[j]=='(')d++; if(s[j]==')')d--; j++;}while(d); out[(*o)++]='('; rev(s,x+1,j-1,out,o); out[(*o)++]=')'; for(int t=j;t<y;t++)out[(*o)++]=s[t];}
    else for(int t=x;t<y;t++) out[(*o)++]=s[t];}
}
int main(int argc,char**argv){char*m=argv[1]; long long mx=atoll(argv[2]); long P=atol(argv[3]); int S=argv[4][0]-'A';
  long long K=argc>6?atoll(argv[6]):20, from=argc>7?atoll(argv[7]):0; int ws=-1; char*ww=0; int wl=0, wo=0; if(argc>8){ws=argv[8][0]-'A'; ww=argv[8]+2; if(*ww=='<'){ww++; wo=-1;} wl=strlen(ww);} int cur=-2; long long curev=0,curt=0;
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*p=m+s*7+r*3; if(p[2]=='-'){ns[s][r]=-1;continue;} nw[s][r]=p[0]-'0'; mv[s][r]=p[1]=='R'?1:-1; ns[s][r]=p[2]-'A';}
  FILE*f=fopen(argv[5],"r"); static char name[1024][64]; static regex_t rl[1024],rr[1024]; int nr=0; char a[4096],b[4096];
  while(fscanf(f,"%63s %4095s %4095s",name[nr],a,b)==3){ char ra[8192]; int o=0; if(!strcmp(a,"-"))a[0]=0; if(!strcmp(b,"-"))b[0]=0; int la=strlen(a); int dollar=0;
    if(la&&a[0]=='^'){dollar=1;} // '^' at start of left = left end of tape
    rev(a,dollar,la,ra,&o); ra[o]=0; char fa[8300]; sprintf(fa,"^%s%s",ra,dollar?"$":""); char fb[8300]; sprintf(fb,"^%s",b);
    if(regcomp(&rl[nr],fa,REG_EXTENDED|REG_NOSUB)||regcomp(&rr[nr],fb,REG_EXTENDED|REG_NOSUB)){fprintf(stderr,"bad rule %s\n",name[nr]);return 1;}
    fprintf(stderr,"rule %s: L~%s R~%s\n",name[nr],fa,fb); nr++;}
  int pend=0; static long long hit[1024]={0}; long long miss=0,ev=0; long long shown=0;
  long pos=N/2,lo=pos,hi=pos; int st=0; long long t=0;
  while(t<mx){int r=tape[pos]; int s2=ns[st][r]; if(s2<0){printf("HALT %lld\n",t+1);break;}
    if(st==S && pos-N/2==P && t>=from){ ev++;
      int nl=0; for(long i=pos-1;i>=lo-64;i--) lbuf[nl++]=48+tape[i]; lbuf[nl]=0;
      int nrr=0; for(long i=pos;i<=hi+64;i++) rbuf[nrr++]=48+tape[i]; rbuf[nrr]=0;
      int k; for(k=0;k<nr;k++) if(!regexec(&rl[k],lbuf,0,0,0)&&!regexec(&rr[k],rbuf,0,0,0)) break;
      cur=k<nr?k:-1; curev=ev; curt=t; if(pend && K>0){pend=0; printf("%lld %lld %ld ",ev,t,lo-N/2); for(long i=lo;i<=hi;i++){if(i==pos)putchar(0x7c); putchar(0x30+tape[i]);} putchar(10);} if(k<nr) hit[k]++; else { miss++; if(shown<K){shown++; pend=1; if(K>0) printf("%lld %lld %ld ",ev,t,lo-N/2); else printf("MISS %lld %lld %ld ",ev,t,lo-N/2); for(long i=lo;i<=hi;i++){if(i==pos)putchar('|'); putchar('0'+tape[i]);} putchar('\n');}}
    }
    if(ws==st){int ok=1; for(int q=0;q<wl;q++) if(tape[pos+wo+q]!=ww[q]-'0'){ok=0;break;} if(ok) printf("WATCH %lld cell %ld lastevent %lld at %lld rule %s\n",t,pos-N/2,curev,curt,cur>=0?name[cur]:(cur==-1?"MISS":"none"));}
    tape[pos]=nw[st][r]; pos+=mv[st][r]; st=s2; t++; if(pos<lo)lo=pos; if(pos>hi)hi=pos;}
  printf("steps %lld events %lld lo %ld hi %ld\n",t,ev,lo-N/2,hi-N/2);
  for(int k=0;k<nr;k++) printf("rule %s %lld\n",name[k],hit[k]); printf("unmatched %lld\n",miss);
}
