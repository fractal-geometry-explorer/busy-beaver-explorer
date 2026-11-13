// tokvisits: run 1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD--- from blank tape and print the tape at each visit of the
// right end in state A as "visit step | c sep c sep ..." (counters (10)^c, separator strings; a leading 1 is the prefix)
// usage: gcc -O2 -o tokvisits tokvisits.c && ./tokvisits MAX_STEPS > visits.txt
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int W[6][2],Mv[6][2],N[6][2];
int main(int argc,char**argv){
  const char*M="1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD---";
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){const char*t=M+7*s+3*r; if(t[0]=='-'){N[s][r]=-1;continue;} W[s][r]=t[0]-'0'; Mv[s][r]=t[1]=='R'?1:-1; N[s][r]=t[2]-'A';}
  long long maxs=atoll(argv[1]); long long SZ=1<<24; unsigned char*tp=calloc(SZ,1); long long pos=SZ/2, lo=pos, hi=pos; int st=0;
  long long v=0;
  for(long long k=1;k<=maxs;k++){
    int sym=tp[pos]; if(N[st][sym]<0){printf("HALT %lld\n",k);return 0;}
    tp[pos]=W[st][sym]; pos+=Mv[st][sym]; st=N[st][sym];
    if(pos<lo)lo=pos; if(pos>hi)hi=pos;
    if(pos<=1||pos>=SZ-2){fprintf(stderr,"tape\n");return 1;}
    if(st==0&&pos==hi&&tp[pos]==0){
      v++; printf("%lld %lld",v,k);
      long long i=lo; while(i<pos&&tp[i]==0)i++;
      // tokenize
      char sep[64]; int sl=0; int first=1;
      while(i<pos){
        if(tp[i]==1&&i+1<pos&&tp[i+1]==0 && !(i+2<pos && tp[i+2]==0 && 0)){
          // count run of 10
          long long c=0; while(i+1<pos && tp[i]==1&&tp[i+1]==0){ c++; i+=2; }
          // a final '1' at pos-1? handled as sep
          if(sl||!first){ sep[sl]=0; printf(" %s",sl?sep:"-"); }
          else if(first){ printf(" |"); }
          sl=0; first=0; printf(" %lld",c);
        } else { if(sl<60) sep[sl++]='0'+tp[i]; i++; if(first){} }
      }
      if(sl){sep[sl]=0; printf(" %s",sep);}
      printf("\n");
    }
  }
  return 0;
}
