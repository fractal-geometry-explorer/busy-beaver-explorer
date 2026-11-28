// Robustness test: the machine run as usual, but at each sweep (first visit of the right end after the left end) every
// clean digit word y=0001111 / z=0111111 between clean words is flipped with probability P. A halt would show that
// non-halting depends on the digit values; none was found.  usage: flip MACHINE STEPS P SEED [START_STATE]
// Run the TM; at each first right-end visit after a left visit, flip clean digit tokens y<->z at random (prob P).
#include <stdio.h>
#include <stdlib.h>
#define T (1<<23)
static unsigned char tape[T];
static long st[1<<20],ln0[1<<20],ln1[1<<20];
int main(int argc,char**argv){
  char*m=argv[1]; long long N=atoll(argv[2]); double P=atof(argv[3]); srand(atoi(argv[4])); int s0=argc>5?atoi(argv[5]):0;
  int w[6][2],d[6][2],n[6][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*x=m+7*s+3*b; if(x[0]=='-'){n[s][b]=-1;continue;} w[s][b]=x[0]-'0'; d[s][b]=x[1]=='R'?1:-1; n[s][b]=x[2]-'A';}
  long p=T/2,lo=p,hi=p; int s=s0; int last=0; long round=0; long flips=0;
  for(long long i=0;i<N;i++){int b=tape[p]; if(n[s][b]<0){printf("HALT step %lld round %ld flips %ld\n",i,round,flips);return 0;} tape[p]=w[s][b]; p+=d[s][b]; s=n[s][b];
    if(p>hi){hi=p; if(last!=1){ last=1; round++;
        if(round>5){ // tokenize
          long q=lo; while(q<=hi&&tape[q]==1)q++; int k=0;
          while(q<=hi){ long a0=q; while(q<=hi&&tape[q]==0)q++; long a1=q; while(q<=hi&&tape[q]==1)q++; if(q==a1)break; st[k]=a0; ln0[k]=a1-a0; ln1[k]=q-a1; k++; }
          for(int j=2;j<k-2;j++){
            int isy= ln0[j]==3&&ln1[j]==4, isz= ln0[j]==1&&ln1[j]==6;
            if(!(isy||isz)) continue;
            int okn=1; for(int t=j-1;t<=j+1;t+=2){ int a=ln0[t],c=ln1[t]; if(!((a==3&&c==1)||(a==3&&c==4)||(a==1&&c==6))) okn=0; }
            if(!okn) continue;
            if(rand()<P*RAND_MAX){ long a=st[j]; if(isy){tape[a+1]=1;tape[a+2]=1;} else {tape[a+1]=0;tape[a+2]=0;} flips++; }
          }
        }}}
    if(p<lo){lo=p; last=-1;}
    if(p<2||p>T-3){printf("OUT\n");return 0;}
  }
  printf("nohalt round %ld flips %ld\n",round,flips); return 0;}
