// match POOL < queries("MACHINE MASK12")  : pool tables agreeing with a relabelled query on all non-wildcard slots
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static uint8_t *pool; static char (*pname)[42]; static int np;
static int enc(const char*t){ if(t[0]=='-')return 255; return (t[0]-'0')*12+(t[1]=='R')*6+(t[2]-'A'); }
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); char line[256]; int cap=1<<18; pool=malloc(cap*12); pname=malloc(cap*42);
  while(fgets(line,sizeof line,f)){ if(strlen(line)<41)continue; if(np==cap){cap*=2;pool=realloc(pool,cap*12);pname=realloc(pname,cap*42);}
    memcpy(pname[np],line,41);pname[np][41]=0; for(int k=0;k<12;k++)pool[np*12+k]=enc(line+(k/2)*7+(k%2)*3); np++; }
  // index pool by slot0 (A0) value to speed up? simple brute force
  int perms[720][6],npm=0; int p[6]={0,1,2,3,4,5};
  // generate perms
  void gen(int k){ if(k==6){memcpy(perms[npm++],p,sizeof p);return;} for(int i=k;i<6;i++){int t=p[k];p[k]=p[i];p[i]=t;gen(k+1);t=p[k];p[k]=p[i];p[i]=t;} }
  gen(0);
  while(fgets(line,sizeof line,stdin)){
    if(strlen(line)<54)continue; char*m=line; char*mask=line+42;
    int h[12]; for(int k=0;k<12;k++)h[k]=enc(m+(k/2)*7+(k%2)*3);
    for(int mir=0;mir<2;mir++)for(int q=0;q<720;q++){
      int *pi=perms[q]; uint8_t t[12]; uint8_t wild[12]; int fixed[12],nf=0;
      for(int k=0;k<12;k++){ int k2=pi[k/2]*2+(k%2); wild[k2]=mask[k]=='*';
        if(h[k]==255) t[k2]=255; else { int w=h[k]/12, d=(h[k]/6)%2, s=h[k]%6; t[k2]=w*12+(d^mir)*6+pi[s]; } }
      for(int k=0;k<12;k++) if(!wild[k]) fixed[nf++]=k;
      for(int i=0;i<np;i++){ uint8_t*P=pool+i*12; int ok=1; for(int j=0;j<nf;j++) if(P[fixed[j]]!=t[fixed[j]]){ok=0;break;}
        if(ok){ int nd=0; char diff[64]="";  for(int k=0;k<12;k++) if(P[k]!=t[k]){nd++; char b[8]; sprintf(b,"%c%d,",'A'+k/2,k%2); strcat(diff,b);} 
          printf("%.41s %s %s mir=%d perm=%d%d%d%d%d%d nd=%d pooldiff=%s\n",m,mask,pname[i],mir,pi[0],pi[1],pi[2],pi[3],pi[4],pi[5],nd,diff); } }
    }
  }
}
