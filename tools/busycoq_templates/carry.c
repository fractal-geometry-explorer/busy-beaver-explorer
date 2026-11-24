// Mine "carry rules" of a 6-state 2-symbol TM:
//   E D1^n <{{Q}} M   -->+   F D0^n <* M' {{Q'}}>      (head starts on the last cell of D1^n (or E if n=0),
// for n = 0..NMAX, never leaving the region on the far (left) side, ending at the first arrival
// on the cell just right of M.  Right-side rules: run the mirrored machine.
// Output: machine side Q M E D1 -> Q' M' F D0
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#define NMAX 6
int wr[6][2], mv[6][2], nx[6][2]; // mv: +1 right, -1 left; nx -1 halt
static void parse(const char*s,int mirror){
  for(int q=0;q<6;q++)for(int b=0;b<2;b++){const char*t=s+q*7+b*3;
    if(t[0]=='-'){wr[q][b]=1;mv[q][b]=1;nx[q][b]=-1;continue;}
    wr[q][b]=t[0]-'0';mv[q][b]=(t[1]=='R')?1:-1;if(mirror)mv[q][b]=-mv[q][b];nx[q][b]=t[2]-'A';}
}
// region cells [0,len), head at h, state q. run until head==len (exit right) -> return state, or -1
static int run(int*tape,int len,int h,int q,long cap){
  for(long s=0;s<cap;s++){
    if(h<0)return -1; if(h==len)return q;
    int b=tape[h]; int nq=nx[q][b]; if(nq<0)return -1;
    tape[h]=wr[q][b]; h+=mv[q][b]; q=nq;
  }
  return -1;
}
static void bits(char*o,unsigned v,int l){for(int i=0;i<l;i++)o[i]='0'+((v>>(l-1-i))&1);o[l]=0;}
int main(int argc,char**argv){
  char line[256];
  while(fgets(line,sizeof line,stdin)){
    char *m=line; while(*m==' '||(*m>='0'&&*m<='9'&&line[0]!='1'))m++;
    // input: one machine string per line
    line[strcspn(line,"\r\n ")]=0;
    for(int side=0;side<2;side++){
      parse(line,side);
      for(int q=0;q<6;q++)
      for(int ml=0;ml<=2;ml++)for(unsigned mw=0;mw<(1u<<ml);mw++)
      for(int w=1;w<=4;w++)for(unsigned d1=0;d1<(1u<<w);d1++)
      for(int el=0;el<=w;el++)for(unsigned e=0;e<(1u<<el);e++){
        int ok=1,qq=-1; int tape[64],F[8],D0[8],M2[8];
        for(int n=0;n<=NMAX&&ok;n++){
          int len=0;
          for(int i=0;i<el;i++)tape[len++]=(e>>(el-1-i))&1;
          for(int k=0;k<n;k++)for(int i=0;i<w;i++)tape[len++]=(d1>>(w-1-i))&1;
          int h=len-1; if(h<0){ok=0;break;}
          for(int i=0;i<ml;i++)tape[len++]=(mw>>(ml-1-i))&1;
          int r=run(tape,len,h,q,20000);
          if(r<0){ok=0;break;}
          if(n==0){qq=r;for(int i=0;i<el;i++)F[i]=tape[i];for(int i=0;i<ml;i++)M2[i]=tape[el+i];}
          else{
            if(r!=qq){ok=0;break;}
            for(int i=0;i<el;i++)if(tape[i]!=F[i])ok=0;
            for(int i=0;i<ml;i++)if(tape[el+n*w+i]!=M2[i])ok=0;
            if(n==1)for(int i=0;i<w;i++)D0[i]=tape[el+i];
            for(int k=0;k<n;k++)for(int i=0;i<w;i++)if(tape[el+k*w+i]!=D0[i])ok=0;
          }
        }
        if(!ok)continue;
        // nontrivial: D0 != D1
        unsigned d0=0;for(int i=0;i<w;i++)d0=d0*2+D0[i];
        if(d0==d1)continue;
        // skip non-primitive D1 (period divides w) to cut duplicates
        int prim=1;for(int p=1;p<w;p++)if(w%p==0){unsigned mask=(1u<<p)-1;unsigned blk=d1&mask;int all=1;for(int k=0;k<w/p;k++)if(((d1>>(k*p))&mask)!=blk)all=0; unsigned blk0=d0&mask;int all0=1;for(int k=0;k<w/p;k++)if(((d0>>(k*p))&mask)!=blk0)all0=0; if(all&&all0)prim=0;}
        if(!prim)continue;
        char sE[8],sD1[8],sF[8],sD0[8],sM[8],sM2[8];
        bits(sE,e,el);bits(sD1,d1,w);bits(sD0,d0,w);bits(sM,mw,ml);
        for(int i=0;i<el;i++)sF[i]='0'+F[i];sF[el]=0;for(int i=0;i<ml;i++)sM2[i]='0'+M2[i];sM2[ml]=0;
        printf("%s %c %c M=%s E=%s D1=%s -> %c M'=%s F=%s D0=%s\n",line,side?'R':'L','A'+q,sM,sE,sD1,'A'+qq,sM2,sF,sD0);
      }
    }
  }
}
