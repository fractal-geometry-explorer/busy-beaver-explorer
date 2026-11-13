#include <stdio.h>
#include <stdlib.h>
#include <string.h>
/* Perturbation test: does the machine still avoid halting when the block lengths of a real configuration are
   replaced by other values?
   usage: pert MACHINE WORD "TAPE" TRIALS STEPS MAXN MINN SEED [MOD]
   TAPE is a configuration in the format of events.c ("^n" = n copies of WORD, digits are cells, "S>" marks the
   head in state S on the next cell).  Trial 0 runs TAPE as given; every later trial replaces each count n >= MINN
   by a random value in [MINN, MAXN] (with the same residue mod MOD if MOD is given), runs STEPS steps and reports a
   halt with the counts used.  A count below MINN is kept: small counts are part of the marker shapes. */
int main(int argc,char**argv){
  const char*m=argv[1]; const char*wd=argv[2]; char*spec=argv[3]; int trials=atoi(argv[4]); long long N=atoll(argv[5]); int maxn=atoi(argv[6]); int minn=atoi(argv[7]); srand(atoi(argv[8]));
  int wl=strlen(wd);
  int W[6][2],Dd[6][2],S[6][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*x=m+s*7+b*3; if(x[2]=='-'){S[s][b]=-1;continue;} W[s][b]=x[0]-'0';Dd[s][b]=x[1]=='R'?1:-1;S[s][b]=x[2]-'A';}
  // parse tokens
  char *tok[4096]; int nt=0; char buf[1<<16]; strcpy(buf,spec);
  for(char*p=strtok(buf," ");p;p=strtok(NULL," ")) tok[nt++]=p;
  long L=1<<24; unsigned char*t=malloc(L);
  int halts=0; static char cnts[65536];
  for(int tr=0;tr<trials;tr++){
    memset(t,0,L); cnts[0]=0; long p=L/2; long pos=p; int st=-1; long hp=0;
    for(int i=0;i<nt;i++){ char*s=tok[i];
      // literal if contains '>' or starts with digit 0/1 sequences? numbers >=2 or multi-digit decimal
      int lit = (s[0]!='^');
      if(lit){ for(char*c=s;*c;c++){ if(*c=='>'){continue;} if(*c>='A'&&*c<='F'){st=*c-'A'; hp=pos; continue;} t[pos++]=*c-'0'; } }
      else { int n=atoi(s+1); int n2=n; if(tr>0 && n>=minn){ n2 = minn+rand()%(maxn-minn+1); if(argc>9){int md=atoi(argv[9]); n2 = n2 - (n2 % md) + (n % md); if(n2<minn) n2+=md;}} for(int k=0;k<n2;k++) for(int j=0;j<wl;j++) t[pos++]=wd[j]-'0'; sprintf(cnts+strlen(cnts),"%d ",n2);}
    }
    long pp=hp; char desc[4096]; desc[0]=0; int s=st; long long n;
    for(n=0;n<N;n++){ int b=t[pp]; int ns=S[s][b]; if(ns<0){halts++; printf("trial %d HALT after %lld: %s\n",tr,n,cnts); break;} t[pp]=W[s][b]; pp+=Dd[s][b]; s=ns; if(pp<1||pp>L-2){printf("edge\n");break;} }
  }
  printf("halts %d / %d\n",halts,trials);
}
