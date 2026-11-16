/* evrun MACHINE MAXSTEPS STATE SIDE CKPT_IN|- CKPT_OUT
 *
 * Direct simulation from blank tape (CKPT_IN "-") or from a checkpoint, printing "STEPS cells" (the head's cell in
 * brackets) each time the head, in STATE, is at the left (SIDE L) or right (SIDE R) end of the visited cells, and
 * writing a checkpoint (step count, head, ends, state, tape) at MAXSTEPS, so that a long run can be done in pieces.
 * The same loop as tools/c/tmrun.c (`at S L|R`), with a resumable state; steps follow the bbchallenge count.
 * Used for 1RB0RE_1LC0RA_1RE1LD_0LB0LF_1RA1RA_0LD--- with STATE A, SIDE R (the round ends of py/epoch.py).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define W (1<<16)
static uint8_t tape[W];
int main(int argc,char**argv){
  if(argc<7){fprintf(stderr,"usage: evrun MACHINE MAXSTEPS STATE L|R CKPT_IN|- CKPT_OUT\n");return 1;}
  const char*m=argv[1]; long long max=atoll(argv[2]); int es=argv[3][0]-'A'; int side=argv[4][0]=='R';
  int wr[16][2],mv[16][2],nx[16][2]; int q=0;
  for(const char*p=m;*p;){for(int b=0;b<2;b++){if(p[0]=='-'){wr[q][b]=-1;}else{wr[q][b]=p[0]-'0';mv[q][b]=p[1]=='R'?1:-1;nx[q][b]=p[2]-'A';}p+=3;}q++;if(*p=='_')p++;}
  int WR[32],MV[32],NX[32]; for(int i=0;i<q;i++)for(int b=0;b<2;b++){WR[i*2+b]=wr[i][b];MV[i*2+b]=mv[i][b];NX[i*2+b]=nx[i][b];}
  long long n=0; int h=W/2,lo=W/2,hi=W/2,st=0;
  if(strcmp(argv[5],"-")){FILE*f=fopen(argv[5],"rb"); if(!f||fread(&n,8,1,f)!=1||fread(&h,4,1,f)!=1||fread(&lo,4,1,f)!=1||fread(&hi,4,1,f)!=1||fread(&st,4,1,f)!=1||fread(tape,1,W,f)!=W){fprintf(stderr,"bad checkpoint\n");return 1;} fclose(f);}
  int halted=0;
  while(n<max){
    int k=(st<<1)|tape[h]; if(WR[k]<0){halted=1;n++;break;}
    tape[h]=WR[k]; h+=MV[k]; st=NX[k]; n++;
    if(h<lo)lo=h; if(h>hi)hi=h;
    if(__builtin_expect(st==es,0) && h==(side?hi:lo)){
      printf("%lld ",n); for(int i=lo;i<=hi;i++){ if(i==h) printf("[%c]",'0'+tape[i]); else putchar('0'+tape[i]);} putchar('\n'); fflush(stdout);
    }
    if(h<2||h>W-3){fprintf(stderr,"tape overflow\n");return 2;}
  }
  printf("%s %lld\n",halted?"halted":"running",n);
  FILE*f=fopen(argv[6],"wb");fwrite(&n,8,1,f);fwrite(&h,4,1,f);fwrite(&lo,4,1,f);fwrite(&hi,4,1,f);fwrite(&st,4,1,f);fwrite(tape,1,W,f);fclose(f);
  return 0;
}
