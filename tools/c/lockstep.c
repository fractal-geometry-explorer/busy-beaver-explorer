// lockstep M1 M2 N
//
// Run two machines side by side from blank tape and compare the tape and the head position at every step,
// exactly (a count of differing cells is kept up to date at each write). Does not stop at the first
// difference: two runs can part for a few steps and come together again.
//
// Output, one JSON line: the number of steps 0..N at which tape or head differ, the first and last such step,
// the number of separate episodes, the largest number of differing cells, the pairs of states the machines are
// in while they agree, and the transitions neither run uses.
#include <stdio.h>
#include <stdlib.h>
typedef struct{int w,d,n;} tr;
static void parse(const char*m,tr T[6][2]){for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*t=m+7*s+3*b; if(t[0]=='-'){T[s][b].n=-1;} else {T[s][b].w=t[0]-'0';T[s][b].d=t[1]=='R'?1:-1;T[s][b].n=t[2]-'A';}}}
int main(int c,char**v){ if(c<4){fprintf(stderr,"usage: lockstep M1 M2 N\n");return 2;}
  tr T1[6][2],T2[6][2]; parse(v[1],T1); parse(v[2],T2); long N=atol(v[3]);
  long W=2*N+10; unsigned char*a=calloc(W,1),*b=calloc(W,1); long h1=N+5,h2=N+5; int s1=0,s2=0;
  long diff=0,nd=0,first=-1,last=-1,episodes=0,maxdiff=0,halt=-1; int prev=0; long pairs[6][6]={{0}},u1[6][2]={{0}},u2[6][2]={{0}};
  long t; for(t=0;t<=N;t++){
    int d=(diff||h1!=h2); if(d){nd++; if(first<0)first=t; last=t; if(!prev)episodes++; if(diff>maxdiff)maxdiff=diff;} else pairs[s1][s2]++;
    prev=d; if(t==N)break;
    tr x=T1[s1][a[h1]], y=T2[s2][b[h2]]; u1[s1][a[h1]]++; u2[s2][b[h2]]++;
    if(x.n<0||y.n<0){halt=t;break;}
    diff-=a[h1]!=b[h1]; a[h1]=x.w; diff+=a[h1]!=b[h1];
    diff-=a[h2]!=b[h2]; b[h2]=y.w; diff+=a[h2]!=b[h2];
    h1+=x.d; h2+=y.d; s1=x.n; s2=y.n; }
  printf("{\"m1\":\"%s\",\"m2\":\"%s\",\"steps\":%ld,\"halt\":%ld,\"differing\":%ld,\"first\":%ld,\"last\":%ld,\"episodes\":%ld,\"maxcells\":%ld,\"pairs\":{",v[1],v[2],N,halt,nd,first,last,episodes,maxdiff);
  int k=0; for(int i=0;i<6;i++)for(int j=0;j<6;j++)if(pairs[i][j])printf("%s\"%c-%c\":%ld",k++?",":"",'A'+i,'A'+j,pairs[i][j]);
  printf("},\"unused1\":["); k=0; for(int i=0;i<6;i++)for(int j=0;j<2;j++)if(!u1[i][j])printf("%s\"%c%d\"",k++?",":"",'A'+i,j);
  printf("],\"unused2\":["); k=0; for(int i=0;i<6;i++)for(int j=0;j<2;j++)if(!u2[i][j])printf("%s\"%c%d\"",k++?",":"",'A'+i,j);
  printf("]}\n"); return 0; }
