/* evdump MACHINE MAX [FROM]: print regular even configs: A reading 0, right = 1^m (m=3 or 5) then gaps 0^(3d+2) 1 then blank,
   left = blank 1^(2s) (0 1^(2v+1))*.  Output: step m s : blocks... | digits... */
#include "../../../tools/c/tm.h"
static int blk[1<<20], dig[1<<20];
int main(int argc,char**argv){
  tm_machine m; tm_parse(argv[1],&m); long long max=atoll(argv[2]); long long from=argc>3?atoll(argv[3]):0;
  tm_tape t; tm_tape_init(&t,1<<20); int st=0;
  for(long long k=0;k<max;k++){
    if(st==0 && k>=from && tm_get(&t,t.head)==0){
      long long p=t.head+1; int mm=0; while(tm_get(&t,p)==1){mm++;p++;}
      if(mm==3||mm==5){
        int ok=1,nd=0;
        while(p<=t.hi){ int z=0; while(p<=t.hi&&tm_get(&t,p)==0){z++;p++;} if(p>t.hi) break; int c=0; while(p<=t.hi&&tm_get(&t,p)==1){c++;p++;} if(c!=1||z%3!=2){ok=0;break;} dig[nd++]=(z-2)/3; }
        int nb=0; long long q=t.lo;
        if(ok){ while(q<=t.hi&&tm_get(&t,q)==0) q++; 
          int c=0; while(q<t.head&&tm_get(&t,q)==1){c++;q++;} if(c%2||c==0) ok=0; int s=c/2;
          while(ok&&q<t.head){ if(tm_get(&t,q)!=0){ok=0;break;} q++; if(q==t.head) break; int c2=0; while(q<t.head&&tm_get(&t,q)==1){c2++;q++;} if(c2%2==0){ok=0;break;} blk[nb++]=(c2-1)/2; }
          if(ok){ printf("%lld %d %d :",k,mm,s); for(int i=0;i<nb;i++) printf(" %d",blk[i]); printf(" |"); for(int i=0;i<nd;i++) printf(" %d",dig[i]); printf("\n"); }
        }
      }
    }
    if(!tm_step(&m,&t,&st)){printf("halted %lld\n",k+1);break;}
  }
}
