// reflect MACHINE SCHED Y  (SCHED: entry states used cyclically, call i enters in SCHED[i mod len])
// reflect MACHINE X Y INIT CALLS [print_every]: end-only system: tape cells 0.., head enters cell 0 in X;
// when head leaves left in Y it re-enters in X (one call). Other exit state -> report violation.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define T 50000000
int W[6][2],M[6][2],N[6][2];
unsigned char tape[T];
int main(int argc,char**argv){
  char*s=argv[1]; char*sched=argv[2]; int sl=strlen(sched); int X=sched[0]-'A', Y=argv[3][0]-'A'; char*init=argv[4]; long calls=atol(argv[5]); long pe=argc>6?atol(argv[6]):0;
  for(int q=0;q<6;q++)for(int b=0;b<2;b++){char*p=s+q*7+b*3; if(p[0]=='-'){N[q][b]=-1;continue;}
    W[q][b]=p[0]-'0'; M[q][b]=p[1]=='R'?1:-1; N[q][b]=p[2]-'A';}
  long hi=0; for(int i=0;init[i];i++){tape[i]=init[i]-'0'; hi=i;}
  long pos=0; int q=X; long c=0, steps=0, maxdepth=0;
  while(c<calls){
    int b=tape[pos]; int nq=N[q][b]; if(nq<0){printf("HALT call %ld steps %ld pos %ld\n",c,steps,pos);return 0;}
    tape[pos]=W[q][b]; pos+=M[q][b]; q=nq; steps++;
    if(pos>hi){hi=pos; if(hi>=T-2){printf("OOB\n");return 0;}}
    if(pos>maxdepth)maxdepth=pos;
    if(pos<0){ if(q!=Y){printf("VIOLATION call %ld exit state %c\n",c,'A'+q); return 0;}
      c++; pos=0; q=sched[c%sl]-'A';
      if(pe && c%pe==0){ printf("%ld steps %ld width %ld : ",c,steps,hi+1); for(long i=0;i<=hi&&i<300;i++)putchar('0'+tape[i]); printf("\n"); }
    }
  }
  printf("OK calls %ld steps %ld width %ld\n",c,steps,hi+1);
}
