// Seam tracer for 1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC (README "The odometer"): a B-overflow transient
// from a synthetic start, step by step, with the option of overwriting the block and the window at the moment
// E-mode ends.
// usage: seam w t lo m maxsteps mode [blockdigits [tdigits|- [g]]]
//   start: the steady phase-B visit with V = 2^w - 32 + lo, switch t, i = 7 and block (1011)^m.
//   Prints, at each change of the state in which the head leaves L over the seam (A> / E>), the window (G', t, I)
//   and the low block digits.
//   mode bit 1: print the steady visits (with the number of bounces since the E->A change and the block entries
//               and returns per state since then); bit 2: stop at the first steady visit;
//   bit 4: at the E->A change overwrite the low block digits with blockdigits (lowest first, digits 0 1 2), the four
//          t digits with tdigits (or - to keep them) and G' with the E-mode word number g (0, 1, 2).
//   example: seam 9 0 0 200 400000000 7 21 0000 0     (the travelling "2 1" pattern: 1182 bounces, 232 E-sends)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<26)
static unsigned char *tp; static long pos, lo_, hi_; static int st; static long long n;
static const char *TT="1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC";
static int W[6][2],Mv[6][2],Nx[6][2];
static const char *MA[2]={"110110111010011101110111011011101110111011101","110110111011011101110111011011101110111011101"};
int main(int argc,char**argv){
  int w=atoi(argv[1]),t=atoi(argv[2]),lo=atoi(argv[3]); long m=atol(argv[4]); long long maxs=atoll(argv[5]); int mode=atoi(argv[6]);
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*x=TT+7*s+3*b; if(x[0]=='-'){Nx[s][b]=-1;continue;} W[s][b]=x[0]-'0';Mv[s][b]=x[1]=='R'?1:-1;Nx[s][b]=x[2]-'A';}
  tp=calloc(N,1); long p=N/2;
  // build tape
  char *buf=malloc(1000000); int L=0;
  buf[L++]='1';
  long long V=(1LL<<w)-32+lo;
  for(int j=w-1;j>=1;j--){ buf[L++]='0'+((V>>j)&1); memcpy(buf+L,"01101",5);L+=5;}
  buf[L++]='0'+(V&1); buf[L++]='0'; buf[L++]='1';
  long seamoff=L;
  memcpy(buf+L,MA[t],45);L+=45;
  memcpy(buf+L,"101101101101101",15);L+=15;
  for(long j=0;j<m;j++){memcpy(buf+L,"1011",4);L+=4;}
  buf[L++]='1';buf[L++]='0';
  for(int j=0;j<L;j++) tp[p+j]=buf[j]-'0';
  long seam=p+seamoff; pos=p+L; lo_=p; hi_=pos; st=2; n=0;
  int prevExit=-1; long long ev=0; long nv=0; long long flipev=-1; long long cr[6]={0},crl[6]={0}; long nvflip=-1;
  while(n<maxs){
    // visit detection
    if(st==2 && pos==hi_ && tp[pos]==0){
      // at visit (head at right end on blank)
      nv++;
      if(mode&1){
        // check steady: M region
        int ok=(memcmp(tp+seam,"",0)==0);
        char mm[46]; for(int j=0;j<45;j++) mm[j]='0'+tp[seam+j]; mm[45]=0;
        int tt=-1; if(!strcmp(mm,MA[0]))tt=0; else if(!strcmp(mm,MA[1]))tt=1;
        if(tt>=0 && nv>1){
          // print L words and i
          printf("steady visit %ld step %lld t=%d I=",nv-1,n,tt); for(int j=45;j<60;j++)putchar('0'+tp[seam+j]);
          printf(" blocklen=%ld L=",(pos-seam-62)/4);
          long a=lo_; while(tp[a]==0)a++; 
          long len=seam-a; int pad=(3-len%3)%3; 
          for(long j=a-pad;j<seam;j+=3){ putchar('0'+tp[j]); }
          printf(" finalbounces=%lld visits_since_flip=%ld blk-entries A=%lld E=%lld C=%lld F=%lld returns B=%lld D=%lld C=%lld\n", flipev>=0? ev-flipev+1: -1, nv-nvflip, cr[0],cr[4],cr[2],cr[5],crl[1],crl[3],crl[2]); if(mode&2) return 0;
        }
      }
    }
    int b=tp[pos]; if(Nx[st][b]<0){printf("HALT at %lld\n",n);return 0;}
    long q=pos+Mv[st][b]; tp[pos]=W[st][b]; st=Nx[st][b]; 
    if(pos==seam-1 && q==seam){
      ev++;
      if(prevExit>=0 && st!=prevExit){
        printf("exit change %c->%c visit %ld step %lld ev %lld  G'=",'A'+prevExit,'A'+st,nv-1,n,ev);
        for(int j=0;j<28;j++)putchar('0'+tp[seam+j]); printf(" t=");
        for(int j=28;j<44;j++){putchar('0'+tp[seam+j]);if(j%4==3)putchar(' ');} printf("I=");
        for(int j=44;j<63;j++)putchar('0'+tp[seam+j]); printf(" blk=");
        long e=hi_; 
        for(long j=seam+63;j<e && j<seam+63+4*24;j+=4){ int v=tp[j]*8+tp[j+1]*4+tp[j+2]*2+tp[j+3]; putchar(v==6?'0':v==2?'1':v==14?'2':'?'); }
        printf("\n");
        if(prevExit==4 && st==0){ flipev=ev; nvflip=nv;
          if(mode&4){ const char*d=argv[7]; const char *pat[3]={"0110","0010","1110"};
            for(int j=0;d[j];j++) for(int c=0;c<4;c++) tp[seam+63+4*j+c]=pat[d[j]-'0'][c]-'0';
            if(argc>8 && argv[8][0]!='-'){ const char *tp3[3]={"0011","0001","0111"}; for(int j=0;j<4;j++) for(int c=0;c<4;c++) tp[seam+28+4*j+c]=tp3[argv[8][j]-'0'][c]-'0'; }
            if(argc>9){ const char *g[3]={"0110110001011001100110011011","0110110011011001100110011011","0110110111011001100110011011"}; for(int c=0;c<28;c++) tp[seam+c]=g[argv[9][0]-'0'][c]-'0'; }
          }
        }
      }
      prevExit=st;
    }
    if(flipev>=0){ if(pos==seam+62&&q==seam+63) cr[st]++; if(pos==seam+63&&q==seam+62) crl[st]++; }
    pos=q; n++; if(pos<lo_)lo_=pos; if(pos>hi_)hi_=pos;
  }
  printf("end %lld\n",n); return 0;
}
