// tok MACHINE STEPS MODE ARGS WORDS MAXLINES
// MODE: at S L|R  -> event when head in state S at end of visited
//       rec       -> new record cell either side
// WORDS: name=bits,name=bits  (greedy longest first). head shown as [S] before the cell it reads
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<26)
unsigned char *tp; int nw; char wn[32][16]; char wb[32][64]; int wl[32];
int W[6][2],D[6][2],S[6][2];
void out(long long t,int lo,int hi,int p,int s){
  static char buf[1<<24]; int bl=0;
  // tokenize left part [lo,p) and right [p,hi]
  char prev[64]=""; int cnt=0;
  #define FLUSH if(cnt){ if(cnt==1) bl+=sprintf(buf+bl,"%s ",prev); else bl+=sprintf(buf+bl,"%s^%d ",prev,cnt);} cnt=0;
  for(int part=0;part<2;part++){
    int a= part? p:lo, b= part? hi+1:p;
    if(part){ FLUSH; bl+=sprintf(buf+bl,"%c> ","ABCDEF"[s]); }
    int i=a;
    while(i<b){
      int k; char tokn[64];
      for(k=0;k<nw;k++){ if(i+wl[k]>b) continue; int ok=1; for(int j=0;j<wl[k];j++) if(tp[i+j]!=wb[k][j]-'0'){ok=0;break;} if(ok) break; }
      if(k<nw){ strcpy(tokn,wn[k]); i+=wl[k]; } else { tokn[0]='0'+tp[i]; tokn[1]=0; i++; }
      if(cnt && !strcmp(tokn,prev)) cnt++; else { FLUSH; strcpy(prev,tokn); cnt=1; }
    }
  }
  FLUSH;
  buf[bl]=0; printf("%lld %d %s\n",t,hi-lo+1,buf);
}
int main(int argc,char**argv){
  char*m=argv[1]; long long steps=atoll(argv[2]); char*mode=argv[3];
  int es=-1,eside=0; int ai=4;
  if(!strcmp(mode,"at")){ es=argv[4][0]-'A'; eside=argv[5][0]=='R'; ai=6; } else ai=4;
  char*words=argv[ai]; long long maxl=atoll(argv[ai+1]);
  // parse words
  nw=0; if(strlen(words)>0){ char*w=strdup(words); for(char*tk=strtok(w,",");tk;tk=strtok(NULL,",")){ char*eq=strchr(tk,'='); *eq=0; strcpy(wn[nw],tk); strcpy(wb[nw],eq+1); wl[nw]=strlen(eq+1); nw++; } }
  // sort by length desc
  for(int i=0;i<nw;i++) for(int j=i+1;j<nw;j++) if(wl[j]>wl[i]){ char t[64]; strcpy(t,wn[i]);strcpy(wn[i],wn[j]);strcpy(wn[j],t); strcpy(t,wb[i]);strcpy(wb[i],wb[j]);strcpy(wb[j],t); int x=wl[i];wl[i]=wl[j];wl[j]=x; }
  for(int i=0;i<6;i++) for(int r=0;r<2;r++){ char*g=m+7*i+3*r; if(g[2]<'A'||g[2]>'F'){S[i][r]=-1;continue;} W[i][r]=g[0]-'0'; D[i][r]=g[1]=='R'?1:-1; S[i][r]=g[2]-'A'; }
  tp=calloc(N,1); int p=N/2, lo=p, hi=p, s=0; long long lines=0;
  for(long long t=1;t<=steps;t++){
    int r=tp[p]; if(S[s][r]<0){ printf("HALT %lld\n",t); out(t,lo,hi,p,s); return 0; }
    tp[p]=W[s][r]; p+=D[s][r]; s=S[s][r];
    int rec=0; if(p<lo){lo=p;rec=1;} if(p>hi){hi=p;rec=1;}
    if(p<=10||p>=N-10){ printf("OUT OF TAPE\n"); return 1; }
    if(es>=0){ if(s==es && p==(eside?hi:lo)){ out(t,lo,hi,p,s); if(++lines>=maxl) return 0; } }
    else if(rec){ out(t,lo,hi,p,s); if(++lines>=maxl) return 0; }
  }
  printf("RUNNING %lld\n",steps); return 0;
}
