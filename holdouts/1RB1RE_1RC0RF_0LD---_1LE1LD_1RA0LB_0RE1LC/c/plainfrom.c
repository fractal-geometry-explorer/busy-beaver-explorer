// plain TM simulator from a snapshot file (c/snap.c or c/bacc.cpp format): plainfrom MACHINE SNAP MAXSTEPS [DUMP [CKFILE SECS DONE0]]
// prints HALT and the cells around the head if the machine halts, else writes the final tape to DUMP ("0 head state", tape).
// With CKFILE, every SECS seconds it also saves the current tape in the same format plus a third line with the number of
// steps done so far (DONE0 + steps of this run), by write-then-rename, so a stopped run can resume from CKFILE.
// usage: gcc -O2 -o plainfrom c/plainfrom.c
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
static long cap=200000000;
static void dump(const char*fn,unsigned char*tp,long p,long o,int st,int third,unsigned long long done){
 long a=1,b=cap-2;while(a<p&&!tp[a])a++;while(b>p&&!tp[b])b--;
 char tmp[4096];snprintf(tmp,sizeof tmp,"%s.tmp",fn);FILE*g=fopen(tmp,"w");if(!g)return;
 fprintf(g,"0 %ld %c\n",p-a,'A'+st);for(long i=a;i<=b;i++)fputc('0'+tp[i],g);fputc('\n',g);
 if(third)fprintf(g,"%llu\n",done);
 if(fclose(g)==0)rename(tmp,fn);}
int main(int c,char**v){const char*m=v[1];int W[6][2],M[6][2],N[6][2];
 for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*t=m+s*7+b*3;
  if(t[2]=='-'){N[s][b]=-1;W[s][b]=0;M[s][b]=0;}else{W[s][b]=t[0]-'0';M[s][b]=t[1]=='R'?1:-1;N[s][b]=t[2]-'A';}}
 FILE*f=fopen(v[2],"r");long L,h;char sc;if(!f||fscanf(f,"%ld %ld %c",&L,&h,&sc)!=3){fprintf(stderr,"bad snapshot\n");return 3;}fgetc(f);
 long o=cap/2;unsigned char*tp=calloc(cap,1);long n=0;int ch;
 while((ch=fgetc(f))=='0'||ch=='1')tp[o+L+n++]=ch-'0';fclose(f);
 long p=o+h;int st=sc-'A';unsigned long long mx=strtoull(v[3],0,10),k=0;
 const char*ckf=c>5?v[5]:0;long secs=c>6?atol(v[6]):600;unsigned long long d0=c>7?strtoull(v[7],0,10):0;
 time_t last=time(0);
 fprintf(stderr,"loaded %ld cells, head %ld state %c\n",n,h,sc);
 while(k<mx){
  unsigned long long lim=mx-k; if(lim>(1ULL<<28))lim=1ULL<<28; unsigned long long e=k+lim;
  while(k<e){int b=tp[p];if(N[st][b]<0){printf("HALT after %llu steps: state %c reads %d at offset %ld\n",d0+k+1,'A'+st,b,p-o);
    long a=p-40;for(long i=a;i<p+40;i++)putchar('0'+tp[i]);putchar('\n');return 0;}
   tp[p]=W[st][b];p+=M[st][b];st=N[st][b];k++;if(p<1||p>=cap-1){printf("tape overflow\n");return 2;}}
  if(ckf&&k<mx&&time(0)-last>=secs){dump(ckf,tp,p,o,st,1,d0+k);last=time(0);}}
 printf("no halt in %llu steps, state %c\n",d0+k,'A'+st);
 if(c>4)dump(v[4],tp,p,o,st,0,0);
 return 1;}
