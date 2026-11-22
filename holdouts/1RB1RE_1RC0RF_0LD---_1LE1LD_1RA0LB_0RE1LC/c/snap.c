// usage: snap MACHINE MAXSTEPS EVERY DIR   (gcc -O2 -o snap c/snap.c; DIR must exist)
// Plain simulator from blank tape; every EVERY steps writes DIR/<step>.txt: "L head state" (offsets from the start
// cell) and the tape from the leftmost to the rightmost visited cell. Used for evidence/phases-5e11.txt (py/phases.py).
#include <stdio.h>
#include <stdlib.h>
int main(int c,char**v){const char*m=v[1];double mx=atof(v[2]);unsigned long long E=(unsigned long long)atof(v[3]);
int W[6][2],Mv[6][2],Nx[6][2];
for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*t=m+s*7+b*3;if(t[0]=='-'){Nx[s][b]=-1;continue;}W[s][b]=t[0]-'0';Mv[s][b]=t[1]=='R'?1:-1;Nx[s][b]=t[2]-'A';}
long N=1L<<28;unsigned char*tp=calloc(N,1);long p=N/2,o=N/2,L=p,R=p;int st=0;unsigned long long n=0;char fn[256];
while(n<mx){int b=tp[p];int x=Nx[st][b];if(x<0){printf("HALT %llu\n",n);return 0;}tp[p]=W[st][b];p+=Mv[st][b];st=x;n++;if(p<L)L=p;if(p>R)R=p;
 if(n%E==0){sprintf(fn,"%s/%012llu.txt",v[4],n);FILE*f=fopen(fn,"w");fprintf(f,"%ld %ld %c\n",L-o,p-o,'A'+st);for(long i=L;i<=R;i++)fputc('0'+tp[i],f);fputc('\n',f);fclose(f);fflush(stdout);}}
printf("done %llu L=%ld R=%ld\n",n,L-o,R-o);}
