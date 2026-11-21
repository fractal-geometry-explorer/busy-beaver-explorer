#include <stdio.h>
#include <stdlib.h>
#include <string.h>
// At R-turns (state E): list the blocks (maximal runs of 1s) of the tape; count even-length blocks, excluding the leftmost and rightmost block; classify their positions relative to the head
int main(int argc,char**argv){
  const char*M=argv[1]; long long N=atoll(argv[2]); int s=argv[3][0]-'A'; int show=argc>4?atoi(argv[4]):0;
  int wr[6][2],mv[6][2],nx[6][2];
  for(int q=0;q<6;q++)for(int b=0;b<2;b++){const char*t=M+q*7+b*3; if(t[2]=='-'){nx[q][b]=-1;continue;} wr[q][b]=t[0]-'0'; mv[q][b]=t[1]=='R'?1:-1; nx[q][b]=t[2]-'A';}
  long SZ=1<<25; unsigned char*tp=calloc(SZ,1); long p=SZ/2,lo=p,hi=p; int dir=1; long long hist[10]={0}, tot=0, dz=0; int shown=0;
  long long pos[3]={0};
  for(long long i=0;i<N;i++){int b=tp[p]; if(nx[s][b]<0){printf("HALT %lld\n",i);return 0;}
    int d=mv[s][b];
    if(d!=dir){
      if(dir==1 && s==4){ tot++;
        long L=lo; while(!tp[L])L++; long H=hi; while(!tp[H])H--;
        int ne=0; long q=L; int first=1; int nleft=0,nhead=0,nright=0;
        while(q<=H){ long a=q; while(tp[q])q++; long len=q-a; int last=(q>H);
          if(!first && !last && len%2==0){ ne++; if(a<=p && p<q) nhead++; else if(q<=p) nleft++; else nright++; }
          first=0; int z=0; while(q<=H && !tp[q]){q++;z++;} if(z>1) dz++; }
        hist[ne<9?ne:9]++;
        if(nhead) pos[0]++; if(nleft) pos[1]+=nleft; if(nright) pos[2]+=nright;
        if(ne>2 && shown<show){shown++; printf("step %lld: %d even blocks (left %d head %d right %d)\n",i,ne,nleft,nhead,nright);}
      }
      dir=d;}
    tp[p]=wr[s][b]; p+=d; s=nx[s][b]; if(p<lo)lo=p; if(p>hi)hi=p;}
  printf("R-turns %lld; double zeros inside %lld; number of inner even blocks:",tot,dz); for(int k=0;k<10;k++) printf(" %d:%lld",k,hist[k]); printf("\nturns with even block at head %lld; even blocks left of head %lld, right %lld\n",pos[0],pos[1],pos[2]);
}
