/* The run from blank tape of 1RB1RD_0RC0RD_0LD1LE_1LC0RB_1LF---_1LA0LE, by the pass map and the restart rules
   (README, "The pass map" and "Restarts"; py/passmap.py is the same map in Python, with its checks).

   usage: model PASSES        (gcc -O2 -o model model.c)
   Iterates the pass map on (x, y) from (21, 44) (the 14th right-end event).  At a restart it prints the wall, the
   buffer and the buffer mod 3; buffer = 0 mod 3 merges (the right part is a copy of the run from blank, read from a
   table of the run's own first 975,986 events), 2 mod 3 halts, 1 mod 3 is not decoded and stops the run.  The step
   count is an estimate: about 0.85 W^2 steps a pass (W = 2x + y; measured 0.8 to 1.1 on the simulated passes);
   the printed figure uses 1.166, an upper-end value.  This is a model, checked against the machine on every
   simulated pass, not a proof. */
#include <stdio.h>
#include <stdlib.h>
typedef long long ll;
// returns 0 ok (x,y updated), 1 marker (a,z,c filled), 2 fixpoint
static int step(ll*x,ll*y,ll*ra,ll*rz,ll*rc){
  ll a=2,z=1,b=*x-5,c=*y/2+1;
  while(b&1){ a+=(b-1)/2+1; z+=b-1; b=(z+3)/2; z=-1; c--; }
  a+=b/2+1; z+=b+4; b=c-2;
  if(b<0){ if(b<-2){*ra=a;*rz=z;*rc=c;return 1;} a-=1; z-=2; b+=2; }
  while(!(b&1)){ a+=b/2; z+=b; b=(z+3)/2; z=-1; if(b==2) return 2; }
  a+=(b-1)/2; z+=b-1; *x=a+1; *y=z+5; return 0;
}
int main(int argc,char**argv){
  ll LIM=atoll(argv[1]); int TB=1100000;
  ll *BX=malloc(sizeof(ll)*TB),*BY=malloc(sizeof(ll)*TB);
  // B[1..14] from blank run (indices as in level2.py), B[14]=(21,44)
  ll init[15][2]={{0,0},{2,6},{3,8},{4,10},{-1,-1},{-1,-1},{11,6},{14,8},{16,10},{23,6},{27,8},{16,34},{32,10},{37,8},{21,44}};
  for(int i=0;i<15;i++){BX[i]=init[i][0];BY[i]=init[i][1];}
  ll x=21,y=44,a,z,c; int n=14;
  while(n+1<TB){ if(step(&x,&y,&a,&z,&c)) break; n++; BX[n]=x;BY[n]=y; }
  int FIRST=n+1; printf("blank table to %d\n",FIRST);
  x=21;y=44; ll pass=14; double W2=0; int markers=0;
  while(pass<LIM){
    int r=step(&x,&y,&a,&z,&c);
    if(r==0){pass++; double W=2.0*x+y; W2+=W*W; if((pass&((1LL<<30)-1))==0){printf("pass %lld x %lld y %lld W %.3g steps~%.3g\n",pass,x,y,2.0*x+y,1.166*W2);fflush(stdout);} continue;}
    if(r==2){printf("FIXPOINT at pass %lld x %lld y %lld\n",pass,x,y);break;}
    int j=-c; if(j>60){printf("j too big\n");break;}
    __int128 Y0=((__int128)1<<j)*(z-4)+1; ll X=a-(ll)((((__int128)1<<j)-1)*(z-4)+2*j+1)/2;
    markers++; printf("marker %d at pass %lld x %lld y %lld j %d z %lld wall %lld buffer %lld mod3 %d\n",markers,pass,x,y,j,z,X,(ll)Y0,(int)(Y0%3));
    if(Y0%3==2){printf("HALT predicted\n");break;}
    if(Y0%3==1){printf("nested case\n");break;}
    ll k=(ll)(Y0/3); if(k+1>=FIRST){printf("sub-run longer than blank table\n");break;}
    for(ll i=1;i<=k+1;i++){double W=2.0*BX[i]+BY[i]+Y0+2.0*X; W2+=W*W;} // rough: sub passes cost ~ sub W^2 really; overestimate
    x=X+BX[k+1]; y=BY[k+1]; pass+=k+1; printf("  merged -> %lld %lld\n",x,y); fflush(stdout);
  }
  printf("stopped at pass %lld x %lld y %lld W %.4g, steps (rough) %.3g\n",pass,x,y,2.0*x+y,1.166*W2);
}
