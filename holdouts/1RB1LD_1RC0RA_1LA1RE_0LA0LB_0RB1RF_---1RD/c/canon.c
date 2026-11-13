// canon STEPS : at every R->L turn into state D, parse the tape as X/Y/Z(a,b,c) and print "step md a b c"
#include <stdio.h>
#include <stdlib.h>
#define N (1<<26)
static unsigned char tape[N];
int main(int argc,char**v){
  char*m="1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD"; long long S=atoll(v[1]);
  int w[6][2],d[6][2],ns[6][2];
  for(int i=0;i<6;i++)for(int b=0;b<2;b++){char*s=m+7*i+3*b; if(s[2]=='-'){ns[i][b]=-1;continue;} w[i][b]=s[0]-'0'; d[i][b]=s[1]=='R'?1:-1; ns[i][b]=s[2]-'A';}
  long long pos=N/2,lo=pos,hi=pos; int st=0,ld=0;
  for(long long n=1;n<=S;n++){
    int b=tape[pos]; int t=ns[st][b]; if(t<0){printf("HALT %lld\n",n);return 0;}
    int dd=d[st][b];
    tape[pos]=w[st][b]; pos+=dd; st=t;
    if(pos<lo)lo=pos; if(pos>hi)hi=pos;
    if(dd<0 && ld>0 && st==3){
      // parse right: pos must be 0, then 1^c then zeros to hi
      long long i=pos+1,c=0; int ok=tape[pos]==0;
      while(i<=hi&&tape[i]) {c++;i++;}
      for(;i<=hi;i++) if(tape[i]) ok=0;
      // left, parsed from the left end: 0* 1^a 0{1,2} (10)^b 1 [pos]
      long long q=lo; long long a=0,bb=0; char md='?';
      while(q<pos&&tape[q]==0) q++;
      long long z0=q-lo;
      while(q<pos&&tape[q]==1){a++;q++;}
      if(a>0 && q==pos){ if(a==1){a=0;} else ok=0; }
      long long z=0; while(q<pos&&tape[q]==0){z++;q++;}
      if(a==0 && ok){ // a=0: leading zeros absorbed; the first 1 starts (10)^b 1
        md='X'; q=lo; while(q<pos&&tape[q]==0) q++; a=0;
        // reparse: (10)^b 1
        while(q+1<pos && tape[q]==1 && tape[q+1]==0){bb++;q+=2;}
        if(!(q==pos-1 && tape[q]==1)) ok=0;
      } else {
        if(z==1) md='X'; else if(z==2) md='Y'; else ok=0;
        if(z==0) ok=0;
        while(q+1<pos && tape[q]==1 && tape[q+1]==0){bb++;q+=2;}
        if(!(q==pos-1 && tape[q]==1)) ok=0;
      }
      (void)z0;
      if(ok) printf("%lld %c %lld %lld %lld\n",n,md,a,bb,c);
      else {
        // Z: 1^a 0 D>0 1^c
        long long q=pos-1; int okz=tape[pos]==0 && q>=lo && tape[q]==0; long long a2=0; q--;
        while(q>=lo&&tape[q]){a2++;q--;} for(;q>=lo;q--) if(tape[q]) okz=0;
        long long i2=pos+1,c2=0; while(i2<=hi&&tape[i2]){c2++;i2++;} for(;i2<=hi;i2++) if(tape[i2]) okz=0;
        if(okz&&a2>0) printf("%lld Z %lld 0 %lld\n",n,a2,c2); else printf("%lld OTHER\n",n);
      }
    }
    ld=dd;
  }
  return 0;
}
