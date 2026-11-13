// rec18: 1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA--- from blank tape. At each left record (state B on a new leftmost
// cell) parse the tape as blocks (10)^n and separators; print the record when the first block is <= 2 (resets)
// or every EVERY-th record. Format: "steps recno width | n0 s1 n1 s2 ..." with s = a (110), b (100), or a literal
// word in brackets.  usage: rec18 MAXCELLS MAXSTEPS EVERY
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
static void p128(u128 x){char b[50];int i=49;b[i]=0;if(!x){printf("0");return;}while(x){b[--i]='0'+(int)(x%10);x/=10;}printf("%s",b+i);}
int main(int argc,char**argv){
  long N=atol(argv[1]); double maxs=atof(argv[2]); long every=atol(argv[3]);
  // A0 1RB A1 0LF ; B0 0LC B1 0RE ; C0 0RA C1 1LD ; D0 1LB D1 0LD ; E0 0RA E1 1RC ; F0 1LA F1 ---
  int W[6][2]={{1,0},{0,0},{0,1},{1,0},{0,1},{1,0}};
  int Mv[6][2]={{1,-1},{-1,1},{1,-1},{-1,-1},{1,1},{-1,0}};
  int Nx[6][2]={{1,5},{2,4},{0,3},{1,3},{0,2},{0,-1}};
  unsigned char*t=calloc(N,1); long h=N-N/8,lo=h,hi=h; int s=0; u128 st=0; long rec=0;
  while((double)st<maxs){
    if(h<=1||h>=N-1){printf("OUT OF TAPE\n");break;}
    int c=t[h];
    if(s==5&&c==1){printf("HALT at ");p128(st);printf("\n");return 0;}
    if(s==1&&h<lo){
      lo=h; rec++;
      long j=h+1,n0=0; while(t[j]==1&&t[j+1]==0&&!(t[j+2]==0)){n0++;j+=2;}
      // recount simply: pairs 10 while next pair is 10
      j=h+1;n0=0; while(j+1<=hi&&t[j]==1&&t[j+1]==0&&(j+2>hi||t[j+2]==1)){n0++;j+=2;}
      if(n0<=2||rec%every==0){
        p128(st);printf(" %ld %ld |",rec,hi-lo+1);
        long k=h+1; int cnt=0;
        while(k<=hi&&cnt<60){
          long n=0; while(k+1<=hi&&t[k]==1&&t[k+1]==0&&(k+2>hi||t[k+2]==1)){n++;k+=2;}
          printf(" %ld",n);
          if(k>hi)break;
          if(t[k]==1&&t[k+1]==1&&t[k+2]==0){printf(" a");k+=3;}
          else if(t[k]==1&&t[k+1]==0&&t[k+2]==0&&(k+3>hi||t[k+3]==1)){printf(" b");k+=3;}
          else {printf(" [");int q=0;while(k<=hi&&q<12&&!(t[k]==1&&t[k+1]==0&&t[k+2]==1&&t[k+3]==0)){printf("%d",t[k]);k++;q++;}printf("]");}
          cnt++;
        }
        printf("\n"); fflush(stdout);
      }
    }
    t[h]=W[s][c]; h+=Mv[s][c]; s=Nx[s][c]; st++; if(h<lo&&0)lo=h; if(h>hi)hi=h;
  }
  printf("END ");p128(st);printf(" rec %ld width %ld\n",rec,hi-lo+1);
}
