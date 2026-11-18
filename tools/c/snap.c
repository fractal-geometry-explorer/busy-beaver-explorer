// Direct run that prints the configuration at given step counts (read ascending from stdin): the cells from the
// leftmost 1 to the cell left of the head, the state, and whether every cell from the head on is blank.
// Used by tools/py/regcheck.py to check regaccel.py cell for cell.  usage: snap MACHINE < steps
#include <stdio.h>
#include <stdlib.h>
// reads step counts (ascending) on stdin; at each prints "steps state <cells from leftmost 1 to head-1> rightblank(0/1)"
int main(int c,char**v){char*m=v[1];
 int T[8][2][3],H[8][2];int q=0;char*p=m;
 while(*p){for(int b=0;b<2;b++){if(p[0]=='-'||p[2]-'A'>=8){H[q][b]=1;}else{H[q][b]=0;T[q][b][0]=p[0]-'0';T[q][b][1]=p[1]=='R'?1:-1;T[q][b][2]=p[2]-'A';}p+=3;}q++;if(*p=='_')p++;}
 long long S=1LL<<28; unsigned char*t=calloc(S,1); long long pos=S/2,lo=S/2,hi=S/2; q=0; long long n=0,want;
 while(scanf("%lld",&want)==1){
  while(n<want){int b=t[pos]; if(H[q][b]){printf("HALT %lld\n",n+1);return 0;} t[pos]=T[q][b][0]; if(t[pos]){if(pos<lo)lo=pos;if(pos>hi)hi=pos;} pos+=T[q][b][1]; q=T[q][b][2]; n++; if(pos<=0||pos>=S-1){printf("EDGE\n");return 0;}}
  long long a=lo; while(a<pos && t[a]==0) a++;
  int rb=1; for(long long i=pos;i<=hi;i++) if(t[i]){rb=0;break;}
  printf("%lld %c ",n,'A'+q); for(long long i=a;i<pos;i++) putchar('0'+t[i]); printf(" %d\n",rb);}
 return 0;}
