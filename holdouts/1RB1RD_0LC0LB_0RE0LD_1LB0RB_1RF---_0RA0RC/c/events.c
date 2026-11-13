#include <stdio.h>
#include <stdlib.h>
#include <string.h>
/* The tape each time the run reaches a new cell at the left end (L) or the right end (R), from blank tape.
   usage: events MACHINE STEPS WORD EVERY_L EVERY_R   (print every EVERY_L-th left event, EVERY_R-th right event;
   0 = none).  Runs of at least two copies of WORD are printed as "^n"; "S>" marks the head in state S. */
int main(int argc,char**argv){
  const char*m=argv[1]; long long N=atoll(argv[2]); const char*wd=argv[3]; int wl=strlen(wd);
  int eL=atoi(argv[4]), eR=atoi(argv[5]);
  int W[6][2],Dd[6][2],S[6][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*x=m+s*7+b*3; if(x[2]=='-'){S[s][b]=-1;continue;} W[s][b]=x[0]-'0';Dd[s][b]=x[1]=='R'?1:-1;S[s][b]=x[2]-'A';}
  long L=1<<27; unsigned char*t=calloc(L,1); long p=L/2,lo=p,hi=p; int s=0; long long cl=0,cr=0;
  for(long long n=0;n<N;n++){
    int b=t[p]; int ns=S[s][b]; if(ns<0){printf("HALT %lld\n",n);return 0;}
    t[p]=W[s][b]; p+=Dd[s][b]; s=ns;
    int ev=0; if(p<lo){lo=p; cl++; if(eL&&cl%eL==0)ev='L';} if(p>hi){hi=p; cr++; if(eR&&cr%eR==0)ev='R';}
    if(ev){ printf("%c %lld ",ev,n+1);
      for(long i=lo;i<=hi;){ if(i==p)printf("%c>",'A'+s);
        int k=0; while(i+(k+1)*wl-1<=hi && memcmp(t+i+k*wl,(const unsigned char*)"",0)==0){int ok=1; for(int j=0;j<wl;j++){ if(i+k*wl+j==p && k>0){ok=0;break;} if(t[i+k*wl+j]!=wd[j]-'0'){ok=0;break;}} if(!ok)break; k++;}
        if(k>=2){printf(" ^%d ",k); i+=k*wl;} else {putchar('0'+t[i]); i++;}
      }
      putchar('\n');}
  }
}
