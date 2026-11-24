// For each mined carry rule, measure how the run from blank tape uses it:
// count occurrences of its start pattern (state Q, M on the near side, E D1^n on the far side, head on the last cell)
// within STEPS steps and the largest n seen.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define TAPE (1<<22)
typedef struct{int side,q,ml,el,w;char M[4],E[8],D1[8];long cnt;int nmax;char line[160];}Rule;
Rule R[200000];int nr;
int wr[6][2],mv[6][2],nx[6][2];
static unsigned char tape[TAPE];
int main(int argc,char**argv){
  long STEPS=atol(argv[1]);
  char buf[256];
  while(fgets(buf,sizeof buf,stdin)){
    char tm[64],side,q,M[8],E[8],D1[8];
    // format: tm side Q M=.. E=.. D1=.. -> ...
    char *p=buf; sscanf(p,"%63s %c %c",tm,&side,&q);
    char*m=strstr(p,"M=")+2; int ml=strcspn(m," "); memcpy(M,m,ml);
    char*e=strstr(p,"E=")+2; int el=strcspn(e," "); memcpy(E,e,el);
    char*d=strstr(p,"D1=")+3; int w=strcspn(d," "); memcpy(D1,d,w);
    Rule*r=&R[nr++]; memset(r,0,sizeof *r); strncpy(r->line,buf,159); r->line[strcspn(r->line,"\n")]=0;
    r->side=side=='R';r->q=q-'A';r->ml=ml;r->el=el;r->w=w;
    for(int i=0;i<ml;i++)r->M[i]=M[i]-'0';for(int i=0;i<el;i++)r->E[i]=E[i]-'0';for(int i=0;i<w;i++)r->D1[i]=D1[i]-'0';
    static char cur[64]=""; static int start=0;
    (void)cur;(void)start;
  }
  // group by machine (rules for same machine are contiguous)
  int i=0;
  while(i<nr){
    char tm[64]; sscanf(R[i].line,"%63s",tm); int j=i; while(j<nr){char t2[64];sscanf(R[j].line,"%63s",t2);if(strcmp(t2,tm))break;j++;}
    for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*t=tm+s*7+b*3; if(t[0]=='-'){nx[s][b]=-1;continue;} wr[s][b]=t[0]-'0';mv[s][b]=t[1]=='R'?1:-1;nx[s][b]=t[2]-'A';}
    memset(tape,0,TAPE); long h=TAPE/2; int q=0;
    for(long st=0;st<STEPS;st++){
      if(h<100||h>TAPE-100)break;
      for(int k=i;k<j;k++){Rule*r=&R[k]; if(r->q!=q)continue;
        int dir=r->side?-1:1; // near side direction: L rules: M to the right (+1). R rules (mirrored): M to the left.
        int ok=1; for(int a=0;a<r->ml;a++)if(tape[h+dir*(1+a)]!=r->M[a]){ok=0;break;} if(!ok)continue;
        // far side: positions h, h-dir, ... visual word order for L rules: E D1^n left to right, head on last cell.
        // printed words are in mirrored-visual order for R rules, i.e. reading from far to near; so cell at h-dir*k corresponds to index from the end.
        long pos=h; int n=0; 
        while(n<200){ int good=1; for(int a=0;a<r->w;a++){ if(tape[pos-dir*a]!=r->D1[r->w-1-a]){good=0;break;} } if(!good)break; pos-=dir*r->w; n++; if(pos<50||pos>TAPE-50)break;}
        // need E right after
        int eg=1; for(int a=0;a<r->el;a++) if(tape[pos-dir*a]!=r->E[r->el-1-a]){eg=0;break;}
        if(r->el==0 && n==0) eg=0;
        if(!eg)continue;
        r->cnt++; if(n>r->nmax)r->nmax=n;
      }
      int b=tape[h]; int nq=nx[q][b]; if(nq<0)break; tape[h]=wr[q][b]; h+=mv[q][b]; q=nq;
    }
    for(int k=i;k<j;k++) if(R[k].cnt) printf("%s | cnt=%ld nmax=%d\n",R[k].line,R[k].cnt,R[k].nmax);
    i=j;
  }
}
