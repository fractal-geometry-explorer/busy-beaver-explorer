// Exact simulator for a machine whose tape is  W 1^n  with the run of 1s on the right: the run is a number.
// usage: runsim MACHINE CLIMB RETURN VISITS [mirror] [check]
//   CLIMB: the state that crosses the run to the right unchanged (X1 -> 1RX), with X0 -> 1RY, Y0 -> 0LZ;
//   RETURN: Z, which crosses it back (Z1 -> 1LZ). All four are checked against the table at the start.
//   A climb from the foot with n ones costs 2n+3 steps and leaves n+1 ones, the head in Z on the cell left of the run.
//   mirror=1 reflects the machine first (for a run on the left). check=1 simulates the run cell by cell instead
//   (same output: used to validate the jump).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128;
static void pr128(u128 x){char b[50];int i=49;b[i]=0;if(!x)b[--i]='0';while(x){b[--i]='0'+(int)(x%10);x/=10;}fputs(b+i,stdout);}
#define OFF (1L<<22)
#define CAP (1L<<28)
static unsigned char *t;
int main(int argc,char**argv){
  const char*m=argv[1]; int CL=argv[2][0]-'A', RT=argv[3][0]-'A'; long maxv=atol(argv[4]);
  int mir=argc>5?atoi(argv[5]):0, chk=argc>6?atoi(argv[6]):0;
  int W[6][2],D[6][2],S[6][2];
  for(int i=0;i<6;i++)for(int b=0;b<2;b++){const char*p=m+7*i+3*b; if(p[0]=='-'){S[i][b]=-1;continue;} W[i][b]=p[0]-'0';D[i][b]=(p[1]=='R')?1:-1; if(mir)D[i][b]=-D[i][b]; S[i][b]=p[2]-'A';}
  int Y=S[CL][0];
  if(!(W[CL][1]==1&&D[CL][1]==1&&S[CL][1]==CL&&W[CL][0]==1&&D[CL][0]==1&&W[Y][0]==0&&D[Y][0]==-1&&S[Y][0]==RT&&W[RT][1]==1&&D[RT][1]==-1&&S[RT][1]==RT)){printf("climb rule does not hold\n");return 1;}
  t=calloc(CAP,1);
  long p=OFF, rs=OFF+1, n=0, lo=OFF; int s=0; u128 steps=0; long v=0,nextp=1;
  long minpos=OFF, rs0=rs, n0=0; long ivmin=1L<<60, ivminn=1L<<60, maxdepth=0; long hd[64],he[64]; memset(hd,0,sizeof hd);memset(he,0,sizeof he);
  long eaten_total=0;
  for(;;){
    if(p>=rs){
      if(s==CL&&p==rs&&!chk){
        long ni=n; u128 top=steps+(u128)ni+3;   // the step at which the head is back on the top 1 of the run
        while(rs-1>lo&&t[rs-1]==1){rs--;n++;}   // absorb explicit 1s below the run
        // statistics of the excursion that just ended
        v++;
        long depth=rs0-minpos; if(depth<0)depth=0; int b=0; while((1L<<b)<=depth&&b<62)b++; hd[b]++; if(depth>maxdepth)maxdepth=depth;
        long dn=(n+1)-n0; int e=(int)(1-dn); if(e<0)e=0; if(e>62)e=62; he[e]++;   // net change of the run this visit is 1 - e
        if(minpos<ivmin)ivmin=minpos; 
        steps+=(u128)ni+3+(u128)n; n++; p=rs-1; s=RT;
        if(n<ivminn)ivminn=n;
        if(v==nextp||v==maxv){printf("visit %ld steps ",v);pr128(top);printf(" n=%ld W=%ld cells (foot at %ld) lowest cell touched since last line=%ld deepest excursion=%ld min n=%ld\n",n,rs-lo,rs-OFF,ivmin-OFF,maxdepth,ivminn);fflush(stdout);if(v==nextp)nextp*=2;ivmin=1L<<60;maxdepth=0;ivminn=1L<<60;}
        if(v>=maxv)break;
        rs0=rs; n0=n; minpos=p;
        continue;
      }
      // materialize one cell of the run (or a blank beyond it)
      while(rs<=p){ t[rs]=(n>0); if(n>0)n--; rs++; }
      if(chk&&s==CL&&n==0&&t[p]==0){ // cell-by-cell mode: count a visit when the climbing state reaches the blank end
        v++; if(v==nextp||v==maxv){printf("visit %ld steps ",v);pr128(steps+3);printf("\n");if(v==nextp)nextp*=2;} if(v>=maxv)break; }
    }
    if(p<minpos)minpos=p; if(p<lo){lo=p; if(lo<8){printf("left overflow\n");return 1;}}
    int b=t[p]; if(S[s][b]<0){printf("HALT in state %c reading %d at visit %ld, steps so far ",'A'+s,b,v);pr128(steps);printf(" (+1 for the halting step), n=%ld, cell %ld, foot %ld\n",n,p-OFF,rs-OFF);return 0;}
    t[p]=W[s][b]; p+=D[s][b]; s=S[s][b]; steps++;
    if(n==0) while(rs-1>p&&rs-1>lo&&t[rs-1]==0) rs--;   // blank cells beyond the tape are not kept
    if(rs>CAP-8){printf("right overflow\n");return 1;}
  }
  printf("depth of an excursion below the foot (log2 bins):");for(int b=0;b<40;b++)if(hd[b])printf(" %d:%ld",b,hd[b]);printf("\n");
  printf("cells of the run eaten per visit (run changes by 1 - e):");for(int b=0;b<63;b++)if(he[b])printf(" %d:%ld",b,he[b]);printf("\n");
  return 0;
}
