/* return_count.c: how often the starting pattern of each rule of lean/Return.lean occurs on the run from blank tape of
 * 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD (the head has just moved left, in the rule's state, onto the last cell of
 * the rule's image, with the rule's carry to the right).
 * usage: return_count STEPS        build: gcc -O2 -o return_count return_count.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static const char* PN[]={"ret_A_110100_w01","ret_A_110101_w01","ret_A_110110_w01","ret_C_011010_w01","ret_C_011010_w011","ret_C_011011_w01","ret_C_011011_w011","ret_C_011101_w01","ret_C_011101_w011","ret_E_110110_w01","ret_E_110110_w011","ret_E_110111_w01","ret_E_110111_w011","ret_E_111011_w01","ret_E_111011_w011","ret_E_111101_w01","ret_E_111101_w011","ret_E_111110_w01","ret_E_111110_w011","ret_E_111111_w01","ret_E_111111_w011"};
static const int PS[]={0,0,0,2,2,2,2,2,2,4,4,4,4,4,4,4,4,4,4,4,4};
static const char* PC[]={"11110100","11110101","11110110","11011010","100011010","11011011","100011011","11011101","100011101","11110110","100110110","11110111","100110111","11111011","100111011","11111101","100111101","11111110","100111110","11111111","100111111"};
static const int PH[]={1,1,1,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2};
#define NP 21
int main(int argc,char**argv){
 const char*m="1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD"; int W[6][2],D[6][2],N[6][2];
 for(int s=0;s<6;s++)for(int b=0;b<2;b++){const char*x=m+7*s+3*b; if(x[0]=='-'){N[s][b]=-1;continue;} W[s][b]=x[0]-'0';D[s][b]=x[1]=='R'?1:-1;N[s][b]=x[2]-'A';}
 long long to=atoll(argv[1]); long long S=1LL<<27; unsigned char*t=calloc(S,1); long long p=S/2; int st=0;
 long long cnt[NP]={0}; long long first[NP]; for(int i=0;i<NP;i++) first[i]=-1;
 int len[NP]; for(int i=0;i<NP;i++) len[i]=strlen(PC[i]);
 for(long long k=1;k<=to;k++){ int b=t[p]; int ns=N[st][b]; if(ns<0){printf("HALT\n");return 0;} t[p]=W[st][b]; int d=D[st][b]; p+=d; st=ns;
  if(d<0){ for(int i=0;i<NP;i++){ if(PS[i]!=st) continue; long long a=p-PH[i]; int ok=1; for(int j=0;j<len[i];j++) if(t[a+j]!=PC[i][j]-'0'){ok=0;break;} if(ok){cnt[i]++; if(first[i]<0) first[i]=k;} } }
 }
 for(int i=0;i<NP;i++) printf("%-24s %12lld  first at %lld\n",PN[i],cnt[i],first[i]);
 return 0;}
