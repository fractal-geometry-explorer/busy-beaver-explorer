// plain TM simulator from a snapshot file (c/snap.c or c/bacc.cpp format): plainfrom MACHINE SNAP MAXSTEPS [DUMP]
// prints HALT and the cells around the head if the machine halts, else writes the final tape to DUMP ("0 head state", tape).
// usage: gcc -O2 -o plainfrom c/plainfrom.c
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int c,char**v){const char*m=v[1];int W[6][2],M[6][2],N[6][2];
 for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*t=m+s*7+b*3;
  if(t[2]=='-'){N[s][b]=-1;W[s][b]=0;M[s][b]=0;}else{W[s][b]=t[0]-'0';M[s][b]=t[1]=='R'?1:-1;N[s][b]=t[2]-'A';}}
 FILE*f=fopen(v[2],"r");long L,h;char sc;fscanf(f,"%ld %ld %c",&L,&h,&sc);fgetc(f);
 long cap=200000000,o=cap/2;unsigned char*tp=calloc(cap,1);long n=0;int ch;
 while((ch=fgetc(f))=='0'||ch=='1')tp[o+L+n++]=ch-'0';fclose(f);
 long p=o+h;int st=sc-'A';unsigned long long mx=strtoull(v[3],0,10),k=0;
 fprintf(stderr,"loaded %ld cells, head %ld state %c\n",n,h,sc);
 while(k<mx){int b=tp[p];if(N[st][b]<0){printf("HALT after %llu steps: state %c reads %d at offset %ld\n",k+1,'A'+st,b,p-o);
   long a=p-40;for(long i=a;i<p+40;i++)putchar('0'+tp[i]);putchar('\n');return 0;}
  tp[p]=W[st][b];p+=M[st][b];st=N[st][b];k++;if(p<1||p>=cap-1){printf("tape overflow\n");return 2;}}
 printf("no halt in %llu steps, state %c\n",k,'A'+st);
 if(c>4){long a=1,b=cap-2;while(a<p&&!tp[a])a++;while(b>p&&!tp[b])b--;FILE*g=fopen(v[4],"w");fprintf(g,"0 %ld %c\n",p-a,'A'+st);for(long i=a;i<=b;i++)fputc('0'+tp[i],g);fputc('\n',g);fclose(g);}
 return 1;}
