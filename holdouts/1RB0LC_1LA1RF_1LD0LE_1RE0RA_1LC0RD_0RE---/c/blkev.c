// blkev: direct simulation from blank tape; at every left-end record the tape is read as a list of blocks (10)^n
// (block lengths; -1 a stray 0) and the record is printed whenever the list, apart from its last block, changes:
// those are the ends of the drains.  usage: gcc -O2 -o blkev blkev.c && ./blkev MACHINE MAXSTEPS | grep -v mon
// blkev M maxsteps : at left records parse tape into list of (10)^n block lengths (-1 = literal 0, x1 separators dropped, -2 = '11' double)
// print record whenever list minus last element differs from previous record's.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int W[6][2],Mv[6][2],N[6][2];
long long *A,*B; long long na=0,nb=0;
void pr(const char*tag,long long k,int st,long long rec,long long*L,long long n){
  printf("%s %lld %c %lld n=%lld :",tag,k,'A'+st,rec,n);
  long long i=0; while(i<n){ long long j=i; while(j<n&&L[j]==L[i])j++; if(j-i>1)printf(" %lld^%lld",L[i],j-i); else printf(" %lld",L[i]); i=j;}
  putchar('\n'); fflush(stdout);}
int main(int c,char**v){
  char*m=v[1]; long long max=atoll(v[2]);
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){char*p=m+s*7+r*3; if(p[2]=='-'){N[s][r]=-1;continue;} W[s][r]=p[0]-'0';Mv[s][r]=p[1]=='R'?1:-1;N[s][r]=p[2]-'A';}
  long long S=1LL<<31; unsigned char*t=calloc(S,1); long long h=S/2,lo=h,hi=h; int st=0; long long rec=0;
  A=malloc(sizeof(long long)*50000000); B=malloc(sizeof(long long)*50000000);
  long long pk=0; int pst=0; long long prec=0;
  for(long long k=1;k<=max;k++){
    int r=t[h]; int ns=N[st][r]; if(ns<0){printf("HALT %lld\n",k);pr("halt",k,st,rec,A,na);return 0;}
    t[h]=W[st][r]; h+=Mv[st][r]; st=ns;
    if(h>hi)hi=h;
    if(h<lo){lo=h; rec++;
      nb=0; long long i=lo;
      while(i<=hi+1){ if(t[i]==1&&t[i+1]==0){long long n=0; while(t[i]==1&&t[i+1]==0){n++;i+=2;} B[nb++]=n; if(t[i]==1){i++;} else if(t[i]==0 && i<=hi){B[nb++]=-1;i++;} }
        else if(t[i]==1){B[nb++]=0;i++;} else {B[nb++]=-1;i++;} }
      // compare B[0..nb-2] to A[0..na-2], ignoring leading reservoir changes: compare from the end
      int diff=0;
      // strip leading: find first index where value!=3 after initial prefix; compare tails after reservoir
      long long ia=0; while(ia<na && A[ia]!=10) ia++; long long ib=0; while(ib<nb && B[ib]!=10) ib++;
      if(na-ia!=nb-ib) diff=1; else for(long long q=0;q<nb-ib-1;q++) if(A[ia+q]!=B[ib+q]){diff=1;break;}
      if(diff && rec>1){ pr("before",pk,pst,prec,A+ia,na-ia); pr("after ",k,st,rec,B+ib,nb-ib);}
      if((rec&(rec-1))==0) pr("mon",k,st,rec,B,nb>40?40:nb);
      long long*T=A;A=B;B=T; long long tn=na;na=nb;nb=tn; pk=k;pst=st;prec=rec;
    }
  }
  pr("end",pk,pst,prec,A,na);
  return 0;}
