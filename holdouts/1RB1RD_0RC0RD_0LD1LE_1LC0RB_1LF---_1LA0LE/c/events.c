/* Exact simulator of 1RB1RD_0RC0RD_0LD1LE_1LC0RB_1LF---_1LA0LE that prints the tape at its right-end events.

   usage: events K [TOKENS...]
   The start tape is TOKENS left to right (aN = (10)^N, zN = 0^N, oN = 1^N) with the head just right of them in
   state C reading 0 (the shape of a right-end event); with no tokens it starts from blank tape in state A.
   An event is the head stepping onto a new rightmost cell in state C; the tape left of the head is printed as
   runs: aN for (10)^N, zN for 0^N, oN for 1^N.  Prints K events, or HALT. */
#include <stdio.h>
#include <stdlib.h>
// start from (10)^x 0^y, head right after in state C; print next K C-events (a^x z^y form) 
int main(int argc,char**argv){
  const char*m="1RB1RD_0RC0RD_0LD1LE_1LC0RB_1LF---_1LA0LE";
  if(argc<2){fprintf(stderr,"usage: events K [TOKENS...]   (tokens aN = (10)^N, zN = 0^N, oN = 1^N; none = blank tape)\n");return 1;} int K=atoi(argv[1]); (void)0;
  int W[6][2],D[6][2],S[6][2];
  for(int i=0;i<6;i++)for(int r=0;r<2;r++){const char*t=m+7*i+3*r; if(t[0]=='-'){S[i][r]=-1;continue;} W[i][r]=t[0]-'0';D[i][r]=t[1]=='R'?1:-1;S[i][r]=t[2]-'A';}
  int SZ=1<<24; unsigned char*tp=calloc(SZ,1); int lo=SZ/4,p=lo; int blank=(argc==2); for(int j=2;j<argc;j++){char t=argv[j][0];int n=atoi(argv[j]+1); for(int i=0;i<n;i++){ if(t=='a'){tp[p++]=1;tp[p++]=0;} else if(t=='o') tp[p++]=1; else p++; }} int hi=p,s=blank?0:2; long long st=0;
  int ev=0;
  while(ev<K){
    if(p<lo){lo=p;}
    if(p>hi){hi=p; if(s==2){ev++; printf("%lld:",st);
      int i=lo; while(i<p){ if(tp[i]==1&&i+1<p&&tp[i+1]==0){int k=0;while(i+1<p&&tp[i]==1&&tp[i+1]==0){k++;i+=2;} printf(" a%d",k);} else {int c=tp[i],k=0; while(i<p&&tp[i]==c && !(c==1&&i+1<p&&tp[i+1]==0)){k++;i++;} printf(" %c%d",c?'o':'z',k);} }
      printf("\n");fflush(stdout);}}
    int r=tp[p]; int ns=S[s][r]; if(ns<0){printf("HALT after %lld steps\n",st);return 0;}
    tp[p]=W[s][r]; p+=D[s][r]; s=ns; st++;
  }
}
