// The plain machine from blank tape; records every entry of the head into the leftmost run of 1s from the right:
// the state, the number of cells of the run left of the head (inclusive) and the length of the whole run.
// usage: entries MACHINE MAXSTEPS      prints the first entry of each kind, then the counts per (state, cells).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<26)
static unsigned char t[N];
int main(int argc,char**argv){
  const char*m=argv[1]; double maxs=atof(argv[2]);
  int W[6][2],D[6][2],S[6][2];
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*p=m+7*s+3*b; if(p[0]=='-'){S[s][b]=-1;continue;} W[s][b]=p[0]-'0';D[s][b]=p[1]=='R'?1:-1;S[s][b]=p[2]-'A';}
  long pos=N/2, lo=N/2, st=0; double steps=0; long cnt[6][64]; memset(cnt,0,sizeof cnt);
  long lastprint=0;
  while(steps<maxs){
    int b=t[pos]; if(S[st][b]<0){printf("HALT %.0f\n",steps);break;}
    int ns=S[st][b]; t[pos]=W[st][b]; long np=pos+D[st][b]; 
    if(pos<lo&&t[pos])lo=pos;
    // entering leftmost run from the right: np is a 1, np+1==pos, and all cells lo..np are 1, and pos cell (after write) whatever
    if(D[st][b]<0 && t[np]){
      // check np is in leftmost run: cheap check only when np-lo small
      if(np-lo<60){ long q=lo; while(q<=np&&t[q])q++; if(q>np){ // length of full leftmost run
          long e=np; while(t[e+1])e++; 
          int len=np-lo+1; int full=e-lo+1;
          if(cnt[ns][len]++<1) printf("step %.0f enter state %c remaining %d full %d right-cell %d\n",steps,'A'+ns,len,full,(int)t[pos]);
      }}
    }
    st=ns; pos=np; steps++;
  }
  for(int s=0;s<6;s++)for(int l=0;l<64;l++)if(cnt[s][l])printf("state %c len %d: %ld\n",'A'+s,l,cnt[s][l]);
}
