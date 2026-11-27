// keys: window situations of a real run, in the form contractsat explores them.
// The window is the W cells from the left frontier E (leftmost cell visited so far) on.  A situation is recorded
// when the head has just come back into the window from the right (pos W-1), or has just moved the frontier
// (pos 0), and at the start.  Output: one line per distinct (word, pos, state): word pos state first_step count.
// usage: keys MACHINE L|R W steps   (R mirrors the machine first)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define TAPE (1<<26)
static unsigned char *tape;
typedef struct { char w[130]; int pos, s; long long first, cnt; int used; } Key;
#define HS (1<<20)
static Key *ht; static long nkeys=0;
static int W;
static void rec(long long E, long long pos, int s, long long step){
    char w[130]; for(int i=0;i<W;i++) w[i]='0'+tape[E+i]; w[W]=0;
    uint64_t h=1469598103934665603ULL; for(int i=0;i<W;i++){h^=w[i];h*=1099511628211ULL;} h^=(pos-E)*31+s; h*=1099511628211ULL;
    long i=h&(HS-1);
    while(ht[i].used){ if(ht[i].pos==pos-E&&ht[i].s==s&&!strcmp(ht[i].w,w)){ht[i].cnt++;return;} i=(i+1)&(HS-1);}    
    ht[i].used=1; strcpy(ht[i].w,w); ht[i].pos=pos-E; ht[i].s=s; ht[i].first=step; ht[i].cnt=1; nkeys++;
    if(nkeys>HS/2){fprintf(stderr,"too many keys\n");exit(2);}
}
int main(int argc,char**argv){
    const char*m=argv[1]; int mirror=argv[2][0]=='R'; W=atoi(argv[3]); long long N=atof(argv[4]);
    int wr[6][2],dr[6][2],ns[6][2],S=0;
    for(const char*p=m;;){ for(int b=0;b<2;b++){ if(p[0]=='-'){ns[S][b]=-1;} else {wr[S][b]=p[0]-'0'; dr[S][b]=(p[1]=='R')?1:-1; if(mirror)dr[S][b]=-dr[S][b]; ns[S][b]=p[2]-'A';} p+=3;} S++; if(*p!='_')break; p++; }
    tape=calloc(TAPE,1); ht=calloc(HS,sizeof(Key));
    long long pos=TAPE/2, E=pos; int s=0; long long quarter[4]={0,0,0,0};
    rec(E,pos,s,0);
    for(long long i=1;i<=N;i++){
        int c=tape[pos]; if(ns[s][c]<0){fprintf(stderr,"HALT at %lld\n",i);break;}
        tape[pos]=wr[s][c]; int d=dr[s][c]; s=ns[s][c]; long long old=pos; pos+=d;
        if(pos<E){E=pos; rec(E,pos,s,i);} else if(old==E+W&&pos==E+W-1) rec(E,pos,s,i);
        if(pos<16||pos>TAPE-16){fprintf(stderr,"tape end\n");break;}
        if(i%(N/4)==0) quarter[i/(N/4)-1]=nkeys;
    }
    fprintf(stderr,"keys after each quarter: %lld %lld %lld %lld\n",quarter[0],quarter[1],quarter[2],quarter[3]);
    for(long i=0;i<HS;i++) if(ht[i].used) printf("%s %d %d %lld %lld\n",ht[i].w,ht[i].pos,ht[i].s,ht[i].first,ht[i].cnt);
    return 0;
}
