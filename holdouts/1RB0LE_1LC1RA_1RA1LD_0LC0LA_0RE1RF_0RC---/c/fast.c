// Batched iterator for DeepMind's map of 1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC--- (lean/DMMap.lean).
// Same orbit and counters as far.c, but runs of "left steps" are jumped L at a time with precomputed affine tables.
//
// A left step starts at C(m, k, b) with k <= 1, m >= 3, q = m/3, r = m%3 and q <= b - 2.  The sweep runs q times to
// C(r, k + 2q, b - q) and the small-left clause (b - q >= 2) gives C(4q + 2k + 2 + 2[r==1], 1, b - q - 2).
// For L consecutive left steps (first with flag k, then k = 1), m = 3^L Q + R gives
//   m_L = 4^L Q + A,  b_L = b - (4^L - 3^L) Q - Cq,   with A, Cq depending on (k, L, R),
// and the steps are all left steps iff b_L >= 0 (b decreases, q increases along the run) and m >= 3.
// We demand b_L >= 101 so that every jumped sweep start has m - 3b <= -300 (outside the near-miss window and
// outside the |m - 3b - 1| <= 100 histogram), so all statistics agree exactly with far.c.
// The two shortcuts are left_step and wall_step of lean/Batch.lean.  The orbit, the wall and sweep-start counts, the
// near-miss lines and the |m - 3b - 1| <= 100 histograms agree exactly with far.c (checked to 3e8 walls); only the
// heuristic sum 1/B is approximated inside a jumped run (trapezoid rule), and t, n are doubles.  The jumped counter
// is not kept across a resume.  About 1.9x the speed of far.c (4.4e7 walls per second on a 2.3 GHz Xeon).
// usage: gcc -O2 -march=native -o fast fast.c -lm && ./fast SECONDS [checkpoint-file]
//   resumes from the checkpoint if it exists, rewrites it every CKI seconds and at the end; STOPW=W stops at wall W.
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include <string.h>
typedef unsigned long long u64; typedef long long i64; typedef __int128 i128;
#define LM 9
#ifndef PI
#define PI 120
#endif
#ifndef CKI
#define CKI 240
#endif
static u64 P3[LM+1], P4[LM+1];
// tables: idx [k][L][R]
static u64 *TA[2][LM+1], *TC[2][LM+1], *TN[2][LM+1];   // m_L = 4^L Q + A ; b decrease = (4^L-3^L) Q + C ; n inc = (4^L-3^L)/1*? see below
static double *T0[2][LM+1], *T1[2][LM+1], *T2[2][LM+1]; // t inc = T2 Q^2 + T1 Q + T0
static u64 NQ[LM+1]; static double CL[LM+2]; static double INV3[LM+1]; // n inc = NQ*Q + TN
// formal L steps from m (any), flag k: returns m_L, total b decrease, n inc, t inc (exact, i128)
static void formal(i128 m, int k, int L, i128*mo, i128*bd, i128*ni, i128*ti){
  i128 bdec=0,n=0,t=0;
  for(int s=0;s<L;s++){ i128 q=m/3; int r=(int)(m%3); i128 K=k+2*q;
    t += q*(6*k+9)+6*q*(q-1) + (r==0? 4*K+8 : r==1? 4*K+34 : 4*K+18);
    n += q+1; bdec += q+2; m = 4*q+2*k+2+(r==1?2:0); k=1; }
  *mo=m;*bd=bdec;*ni=n;*ti=t;
}
static void build(void){
  P3[0]=P4[0]=1; for(int i=1;i<=LM;i++){P3[i]=P3[i-1]*3;P4[i]=P4[i-1]*4;}
  for(int L=1;L<=LM+1;L++){ CL[L]=pow(4.0/3.0,L)-1; if(L<=LM) INV3[L]=1.0/pow(3.0,L); }
  for(int k=0;k<2;k++) for(int L=1;L<=LM;L++){ u64 n3=P3[L];
    TA[k][L]=malloc(8*n3);TC[k][L]=malloc(8*n3);TN[k][L]=malloc(8*n3);
    T0[k][L]=malloc(sizeof(double)*n3);T1[k][L]=malloc(sizeof(double)*n3);T2[k][L]=malloc(sizeof(double)*n3);
    for(u64 R=0;R<n3;R++){ i128 mo[3],bd[3],ni[3],ti[3];
      for(int Q=0;Q<3;Q++) formal((i128)Q*n3+R + (i128)n3*3, k, L, &mo[Q],&bd[Q],&ni[Q],&ti[Q]); // Q offset 3 keeps q>=1 formally
      // values at Q'=Q+3; shift back to Q'=0 base: affine/quadratic in Q'
      i128 dm=mo[1]-mo[0], db=bd[1]-bd[0], dn=ni[1]-ni[0];
      if(dm!=(i128)P4[L] || db!=(i128)(P4[L]-P3[L]) || mo[2]-mo[1]!=dm || bd[2]-bd[1]!=db || ni[2]-ni[1]!=dn){fprintf(stderr,"table not affine\n");exit(1);}
      NQ[L]=(u64)dn;
      TA[k][L][R]=(u64)(mo[0]-3*dm); TC[k][L][R]=(u64)(bd[0]-3*db); TN[k][L][R]=(u64)(ni[0]-3*dn);
      i128 d1=ti[1]-ti[0], d2=ti[2]-2*ti[1]+ti[0]; // t(Q'+3)= a(Q'+3)^2 + c(Q'+3) + e, second difference 2a
      if(d2%2){fprintf(stderr,"odd 2nd diff\n");exit(1);} i128 a=d2/2; i128 c=d1-a*(2*3+1); i128 e=ti[0]-a*9-c*3;
      T2[k][L][R]=(double)a; T1[k][L][R]=(double)c; T0[k][L][R]=(double)e;
    } }
}
static inline u64 divp3(u64 m,int L){ switch(L){case 1:return m/3;case 2:return m/9;case 3:return m/27;case 4:return m/81;
  case 5:return m/243;case 6:return m/729;case 7:return m/2187;case 8:return m/6561;default:return m/19683;} }
int main(int argc,char**argv){
  double budget=atof(argv[1]); u64 stopw=getenv("STOPW")?strtoull(getenv("STOPW"),0,10):0; const char*ck=argc>2?argv[2]:0;
  build();
  u64 m=0,k=0,b=2, walls=0, starts=0, near=0, jumped=0;
  double n=0, t=2, heur=0; static u64 dec[200], decb[40];
  if(ck){ FILE*f=fopen(ck,"rb"); if(f){ if(fread(&m,8,1,f)&&fread(&k,8,1,f)&&fread(&b,8,1,f)&&fread(&walls,8,1,f)&&fread(&starts,8,1,f)&&fread(&near,8,1,f)
      &&fread(&n,sizeof n,1,f)&&fread(&t,sizeof t,1,f)&&fread(&heur,sizeof heur,1,f)&&fread(dec,8,200,f)&&fread(decb,8,40,f)) printf("resumed m=%llu k=%llu b=%llu walls=%llu n=%.4e t=%.4e\n",m,k,b,walls,n,t); fclose(f);} }
  time_t t0=time(0), lastp=t0, lastck=t0;
  for(;;){
    // batched left steps
    if(k<=1 && m>=3 && b>=1 && m/3+2<=b){
      int L=1; { double md=(double)m, bd0=(double)b-101-2*LM; for(int i=2;i<=LM;i++) L += (md*CL[i]<=bd0); }
      while(L>=1){ u64 Q=(u64)((double)m*INV3[L]); i64 Rs=(i64)(m-Q*P3[L]); while(Rs<0){Q--;Rs+=P3[L];} while(Rs>=(i64)P3[L]){Q++;Rs-=P3[L];} u64 R=(u64)Rs; i128 bd=(i128)(P4[L]-P3[L])*Q+TC[k][L][R];
        if((i128)b-bd>=101){ double Qd=(double)Q; u64 nk=1;
          // per step: one sweep start (q>=1 since m>=3 holds along the run), heur sums skipped exactly? no: see below
          starts+=L; (void)nk;
          t += T2[k][L][R]*Qd*Qd + T1[k][L][R]*Qd + T0[k][L][R]; n += (double)NQ[L]*Qd + TN[k][L][R];
          // heur: approximate the L terms 1/(b_i+1) by L/(b+1) .. we do exact: recompute b_i cheaply is not available; use endpoints
          { u64 bL=(u64)((i128)b-bd); heur += L*0.5*(1.0/(b+1)+1.0/(bL+1)); b=bL; }
          m = P4[L]*Q+TA[k][L][R]; k=1; jumped+=L; break; }
        L--; }
      if(L>=1) continue;
    }
    if(b>=1 && m>3*b+101){ // fast wall: sweep b times, then the wall clause
      starts++; heur += 1.0/(double)(b+1);
      t += (double)b*(6.0*k+9) + 6.0*(double)b*(double)(b-1); n += (double)b;
      u64 K=k+2*b; m = m-3*b+1; t += 4.0*K+3; b = 2*K+2; k=0; n+=1; walls++;
      if(stopw && walls==stopw) break;
      if((walls&0xFFFFF)==0) goto report;
      continue; }
    if(b>=1 && m>=3){
      long long d=(long long)m-3*(long long)b; starts++;
      if(d>=-1 && d<=3){ near++; if(near<=200) printf("near miss d=M-3B=%lld at sweep start M=%llu B=%llu (n=%.3e t=%.3e)\n",d,m,b,n,t); fflush(stdout);}
      if(d==1){printf("HALT CRITERION n=%.4e t=%.4e M=%llu B=%llu\n",n,t,m,b);return 0;}
      if(d>=-99 && d<=101){ int e=0; double x=t; while(x>=10){x/=10;e++;} dec[e]++; int eb=0; u64 y=b; while(y>=10){y/=10;eb++;} decb[eb]++; }
      heur += 1.0/(double)(b+1);
      u64 j = m/3 < b ? m/3 : b;
      t += (double)j*(6.0*k+9) + 6.0*(double)j*(double)(j-1); m-=3*j; k+=2*j; b-=j; n+=j; continue;
    }
    if(b==0){ t+=4.0*k+3; m=m+1; b=2*k+2; k=0; n+=1; walls++;
      if(stopw && walls==stopw) break;
      if((walls&0xFFFFF)==0){ report:; time_t now=time(0); if(now-lastp>=PI){ lastp=now;
        printf("n=%.4e walls=%llu starts=%llu jumped=%llu t=%.4e m=%llu b=%llu sum1/B=%.4f el=%lds\n",n,walls,starts,jumped,t,m,b,heur,(long)(now-t0)); fflush(stdout);
        if(ck && (now-lastck>=CKI || now-t0>budget)){ lastck=now; char tmp[512]; snprintf(tmp,512,"%s.tmp",ck); FILE*f=fopen(tmp,"wb");
          fwrite(&m,8,1,f);fwrite(&k,8,1,f);fwrite(&b,8,1,f);fwrite(&walls,8,1,f);fwrite(&starts,8,1,f);fwrite(&near,8,1,f);
          fwrite(&n,sizeof n,1,f);fwrite(&t,sizeof t,1,f);fwrite(&heur,sizeof heur,1,f);fwrite(dec,8,200,f);fwrite(decb,8,40,f);fclose(f);rename(tmp,ck);}
        if(now-t0>budget) break; } }
      if(m>(1ULL<<60)||b>(1ULL<<60)){printf("overflow guard\n");break;}
      continue; }
    if(m==0){ if(b==1){t+=4.0*k+7; m=2*k+3; k=0; b=2;} else {t+=4.0*k+8; m=2*k+2; k=1; b-=2;} }
    else if(m==1){ if(k==0){t+=4; m=0; b+=2;} else if(b==1){t+=4.0*k+33; m=2*k+5;k=0;b=2;} else {t+=4.0*k+34; m=2*k+4;k=1;b-=2;} }
    else { if(k==0){ if(b==1){t+=8; m=0;k=1;b=0;} else {printf("HALT n=%.3e t=%.3e\n",n,t); return 0;} }
      else if(k==1){t+=10; m=0;} else if(b==1){t+=4.0*k+17; m=2*k+3;k=0;b=2;} else {t+=4.0*k+18; m=2*k+2;k=1;b-=2;} }
    n+=1;
  }
  for(int e=0;e<200;e++) if(dec[e]) printf("t in [1e%d,1e%d): %llu sweep starts with |M-3B-1|<=100\n",e,e+1,dec[e]);
  for(int e=0;e<40;e++) if(decb[e]) printf("B in [1e%d,1e%d): %llu sweep starts with |M-3B-1|<=100\n",e,e+1,decb[e]);
  printf("END n=%.4e t=%.4e walls=%llu sweep starts=%llu jumped=%llu near misses=%llu m=%llu k=%llu b=%llu\n",n,t,walls,starts,jumped,near,m,k,b);
}
