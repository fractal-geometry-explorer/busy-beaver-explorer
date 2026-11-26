#include <stdio.h>
#include <stdlib.h>
int W[6][2]={{1,1},{1,1},{1,0},{9,1},{1,0},{0,1}};
int M[6][2]={{1,1},{1,-1},{-1,-1},{0,-1},{1,-1},{1,1}};
int Q[6][2]={{1,5},{2,2},{3,4},{9,4},{5,1},{0,4}};
#define N 40000000
unsigned char t[N];
int main(int c,char**v){long T=atol(v[1]);int K=atoi(v[2]);int p=N/2,q=0,lo=p,hi=p;int cnt=0;
for(long n=0;n<T;n++){int a=t[p];if(q==3&&a==0){printf("HALT %ld\n",n);return 0;}
 t[p]=W[q][a];p+=M[q][a];q=Q[q][a];if(p<lo)lo=p;if(p>hi)hi=p;
 if(q==4&&t[p]==1&&t[p-1]==0){int l=lo;while(l<p&&t[l]==0)l++; if(l==p){
   if(cnt++<K){printf("%ld |",n);int i=p;while(i<=hi){int r=0;while(i<=hi&&t[i]==1){r++;i++;}int z=0;while(i<=hi&&t[i]==0){z++;i++;} if(r)printf("%d",r); if(i>hi)break; putchar(z==1?'.':z==2?'|':z==3?'#':'?');}puts("");}}}
}}
