// The event map of 1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF (py/passmap.py) on 64-bit counts, from L [7, 2] (step 66).
// usage: passrun EVENTS.  Stops when the map leaves its checked domain (a small block in the wrong place).
// At each doubling of the event count it prints how close the run came since the last line: among the left-end
// states whose first block is 1, 4 or 7, the smallest second block and how many second blocks were small.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll;
#define M 256
static ll l[M], o[M]; static int n; // L state
static int bad(ll v){ return v==1||v==2||v==3||v==5; }
static int badq(ll v){ return v==0||v==1||v==2||v==3||v==5; }
static void pr(const char*t,ll*a,int k,ll q){ printf("%s [",t); for(int i=0;i<k;i++) printf("%lld%s",a[i],i+1<k?", ":""); printf("] %lld\n",q); }
int main(int c,char**v){ double Nd=atof(v[1]); ll N=(ll)Nd; l[0]=7; l[1]=2; n=2; ll ev=1; ll next=1; int maxn=2; ll near=0; ll minb=1LL<<62, cnt=0, small=0, small5=0, s50=0,s100=0,s200=0;
  while(ev<N){
    // one L step
    int i=0,k=0; ll cur=l[0];
    if(n==1){ pr("LEFT DOMAIN single",l,n,0); break; }
    for(;;){ ll j=cur/3; int r=cur%3;
      if(i>0 && bad(cur)){ printf("event %lld: nested value %lld at position %d\n",ev,cur,i); pr("LEFT DOMAIN L",l,n,0); return 0; }
      if(i==n-1){ // Riii chain
        ll Q=cur-2; ev++;
        for(;;){ if(badq(Q)){ printf("event %lld: right-end block %lld\n",ev,Q); pr("LEFT DOMAIN Riii from L",l,n,Q); pr("X",o,k,Q); return 0; }
          ll t=Q/3; int rr=Q%3; ev++;
          if(rr==2){ o[k++]=t+2; Q=2*t; continue; }
          if(rr==1){ o[k++]=t+1; Q=2*t+3; // Ri
            ev++; o[0]++; memcpy(l,o,k*sizeof(ll)); l[k]=Q-1; l[k+1]=2; n=k+2; break; }
          o[0]++; memcpy(l,o,k*sizeof(ll)); l[k]=t-1; l[k+1]=2*t+5; n=k+2; break; }
        break; }
      if(r==1){ o[k++]=j+1; cur=l[i+1]+2*j; i++; continue; }
      if(r==2){ ll b=l[i+1]+2*j+5; int rest=n-(i+2);
        if(k==0 && j==0){ // first block vanishes
          if(rest>=1){ l[0]=b; l[1]=l[2]+2; memmove(l+2,l+3,(n-3)*sizeof(ll)); n-=1; } else { l[0]=b; l[1]=2; n=2; }
          ev++; break; }
        memmove(l+k+2,l+i+2,rest*sizeof(ll)); memcpy(l,o,k*sizeof(ll)); l[k]=j-1; l[k+1]=b; n=k+2+rest; l[0]++; ev++; break; }
      if(i+2<n){ ll b=l[i+1]+2*j, d=l[i+2]+2; int rest=n-(i+3);
        memmove(l+k+3,l+i+3,rest*sizeof(ll)); memcpy(l,o,k*sizeof(ll)); l[k]=j; l[k+1]=b; l[k+2]=d; n=k+3+rest; l[0]++; ev++; break; }
      { ll Q=l[i+1]+2*j+1; o[k++]=j; ev+=2; o[0]++; memcpy(l,o,k*sizeof(ll)); l[k]=Q-1; l[k+1]=2; n=k+2; break; }
    }
    if((l[0]==1||l[0]==4||l[0]==7)&&n>=2){ if(l[1]<minb) minb=l[1]; cnt++; if(l[1]<1000) small++; if(l[1]<100000) small5++; if(l[1]<=50) s50++; if(l[1]<=100) s100++; if(l[1]<=200) s200++; }
    if(n>maxn) maxn=n; if(n>M-8){ printf("list too long\n"); return 1; }
    if(n>2){ for(int q=1;q<n-1;q++) if(l[q]<=7){ near++; break; } }
    if(ev>=next){ ll tot=0; for(int q=0;q<n;q++) tot+=l[q]; printf("event %lld: ones %lld; since last line: %lld states with first block 1,4,7; min second %lld; <=50: %lld <=100: %lld <=200: %lld <1000: %lld\n",ev,tot,cnt,minb,s50,s100,s200,small); s50=s100=s200=0; minb=1LL<<62; cnt=0; small=0; small5=0; fflush(stdout); while(next<=ev) next*=2; }
  }
  { ll tot=0; for(int q=0;q<n;q++) tot+=l[q]; printf("done: event %lld, %d blocks, %lld ones\n",ev,n,tot); pr("L",l,n,0); }
  return 0; }
