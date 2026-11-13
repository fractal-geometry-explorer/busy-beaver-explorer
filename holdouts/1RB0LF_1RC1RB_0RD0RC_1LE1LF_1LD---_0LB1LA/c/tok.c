// tok MACHINE STEPS STATE SYM L|R MINSTEP MAXLINES SHAPEONLY: at each end event (head in STATE reading SYM, or * / 2 any),
// print the tape as blocks "k/j" (1^k 0^j, "/j" omitted when j=1), equal neighbours run-length coded "xN".
// SHAPEONLY=1: print only when the block sequence (ignoring counts N) differs from the previous event's.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<25)
unsigned char tape[N]; int nx[6][2],wr[6][2],mv[6][2];
static char buf[1<<22], prevshape[1<<22], shape[1<<22];
int main(int argc,char**argv){char*m=argv[1]; long long S=atoll(argv[2]); char st=argv[3][0]; int sy=atoi(argv[4]); char side=argv[5][0]; long long mins=atoll(argv[6]); long maxl=atol(argv[7]); int so=atoi(argv[8]);
 for(int s=0;s<6;s++)for(int b=0;b<2;b++){char*p=m+s*7+b*3; if(p[2]=='-'){nx[s][b]=-1;continue;} wr[s][b]=p[0]-'0'; mv[s][b]=p[1]=='R'?1:-1; nx[s][b]=p[2]-'A';}
 long pos=N/2,lo=pos,hi=pos; int s=0; long lines=0;
 for(long long t=0;t<S;t++){int b=tape[pos];
  if(t>=mins && (st=='*'||s==st-'A') && (sy==2||b==sy) && ((side=='L'&&pos==lo)||(side=='R'&&pos==hi))){
    char *o=buf, *h=shape; long i=lo; char last[64]=""; long cnt=0;
    // leading zeros
    if(!tape[i]){long j=i; while(j<=hi&&!tape[j])j++; o+=sprintf(o,"_%ld ",j-i); h+=sprintf(h,"_ "); i=j;}
    while(i<=hi||cnt){ char tk[64]=""; if(i<=hi){ long j=i; while(j<=hi&&tape[j])j++; long k=j-i; long z=j; while(z<=hi&&!tape[z])z++; long jz=z-j; if(z>hi&&jz==0) sprintf(tk,"%ld/E",k); else if(jz==1) sprintf(tk,"%ld",k); else sprintf(tk,"%ld/%ld",k,jz); i=z; }
      if(cnt && strcmp(tk,last)==0){cnt++; continue;}
      if(cnt){ if(cnt>1){o+=sprintf(o,"%sx%ld ",last,cnt); h+=sprintf(h,"%sx ",last);} else {o+=sprintf(o,"%s ",last); h+=sprintf(h,"%s ",last);} }
      if(tk[0]){strcpy(last,tk); cnt=1;} else cnt=0; }
    if(!so || strcmp(shape,prevshape)){ printf("%lld %c%d | %s\n",t,'A'+s,b,buf); if(++lines>=maxl)return 0; }
    strcpy(prevshape,shape);
  }
  if(nx[s][b]<0){printf("HALT %lld\n",t);return 0;}
  tape[pos]=wr[s][b]; pos+=mv[s][b]; s=nx[s][b]; if(pos<lo)lo=pos; if(pos>hi)hi=pos;}}
