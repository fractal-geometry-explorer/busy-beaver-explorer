// visits.c: how 1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC reads in one state.  usage: gcc -O2 -o visits visits.c && ./visits 1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC STEPS STATE SYM WL WR
// prints a histogram of the windows (WL cells left of the head, WR cells from the head on) seen when the machine is
// in STATE reading SYM in the first STEPS steps from blank tape (with first and last step), or HALT.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<24)
unsigned char tape[N];
int W[6][2],Mv[6][2],Nx[6][2];
typedef struct {char s[64]; long long c, first, last;} E; E ent[100000]; int ne=0;
int main(int argc,char**argv){
  char*m=argv[1]; long long max=atoll(argv[2]); int S=argv[3][0]-'A', B=atoi(argv[4]), wl=atoi(argv[5]), wr=atoi(argv[6]);
  for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*p=m+s*7+b*3; if(p[0]=='-'){Nx[s][b]=-1;continue;} W[s][b]=p[0]-'0';Mv[s][b]=p[1]=='R'?1:-1;Nx[s][b]=p[2]-'A';}
  long long pos=N/2; int st=0;
  for(long long t=1;t<=max;t++){
    int b=tape[pos];
    if(st==S&&b==B){ char w[64]; int k=0; for(long long i=pos-wl;i<pos+wr;i++){ if(i==pos) w[k++]='['; w[k++]='0'+tape[i]; if(i==pos) w[k++]=']';} w[k]=0;
      int j; for(j=0;j<ne;j++) if(!strcmp(ent[j].s,w)) break; if(j==ne){ if(ne<100000){strcpy(ent[ne].s,w);ent[ne].c=0;ent[ne].first=t;ne++;} else j=-1;} if(j>=0){ent[j].c++;ent[j].last=t;} }
    if(Nx[st][b]<0){printf("HALT %lld\n",t);break;}
    tape[pos]=W[st][b]; pos+=Mv[st][b]; st=Nx[st][b];
  }
  for(int j=0;j<ne;j++) printf("%s %lld first %lld last %lld\n",ent[j].s,ent[j].c,ent[j].first,ent[j].last);
}
