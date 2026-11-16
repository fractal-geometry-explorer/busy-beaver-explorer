/* yorbit.c: orbit.c of 1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD with 128-bit step counts, progress lines and
   checkpoints (the run-length tape is saved every REPORT moves).  usage: yorbit MOVES REPORT CKPT */
#define STEPS_T __int128
#include "rle.h"
static void dump(tm *t, ll moves, const char *f) {
  char tmp[4096]; snprintf(tmp, sizeof tmp, "%s.tmp", f); FILE *o = fopen(tmp, "w");
  fprintf(o, "%lld %d %lld %llu %llu %lld %lld\n", moves, t->st, t->pos, (unsigned long long)(t->steps >> 64), (unsigned long long)t->steps, t->L.n, t->R.n);
  for (ll i = 0; i < t->L.n; i++) fprintf(o, "%d %lld\n", t->L.a[i].sym, t->L.a[i].len);
  for (ll i = 0; i < t->R.n; i++) fprintf(o, "%d %lld\n", t->R.a[i].sym, t->R.a[i].len);
  fclose(o); rename(tmp, f); }
static int load(tm *t, ll *moves, const char *f) {
  FILE *in = fopen(f, "r"); if (!in) return 0; unsigned long long hi, lo; ll ln, rn;
  if (fscanf(in, "%lld %d %lld %llu %llu %lld %lld", moves, &t->st, &t->pos, &hi, &lo, &ln, &rn) != 7) exit(4);
  t->steps = ((__int128)hi << 64) | lo; t->L.n = t->R.n = 0;
  for (ll i = 0; i < ln; i++) { int s; ll l; if (fscanf(in, "%d %lld", &s, &l) != 2) exit(4); push(&t->L, s, l); }
  for (ll i = 0; i < rn; i++) { int s; ll l; if (fscanf(in, "%d %lld", &s, &l) != 2) exit(4); push(&t->R, s, l); }
  fclose(in); return 1; }
int main(int argc,char**argv){ tm t; init(&t,"1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD"); ll maxmoves=atoll(argv[1]), rep=atoll(argv[2]);
  ll prev=-1, i=0; if (load(&t, &i, argv[3])) fprintf(stderr, "resumed at move %lld\n", i);
  for(;i<maxmoves;i++){ if(!move(&t)){ printf("HALT at step %.6Le\n",(long double)t.steps); print_tape(&t,stdout); FILE*o=fopen("HALT_FOUND","a"); fprintf(o,"yorbit halt\n"); fclose(o); return 0; }
    if ((i+1) % rep == 0) { dump(&t, i+1, argv[3]); printf("move %lld step %.6Le\n", i+1, (long double)t.steps); fflush(stdout); }
    if(t.st==1 && topsym(&t.R)==0){
      int rb = t.R.n==0 || (t.R.n==1 && t.R.a[0].sym==0);
      if(!rb) continue;
      ll b=0; if(t.L.n>=1 && t.L.a[0].sym==0) b=1;
      if(t.L.n-b==2 && t.L.a[b].sym==1 && t.L.a[b+1].sym==0 && t.L.a[b+1].len==1){
        ll n=t.L.a[b].len; if(n!=prev){ printf("%.0Lf Y %lld\n",(long double)t.steps,n); fflush(stdout); prev=n; } }
    }
  }
  dump(&t, i, argv[3]); printf("stopped at move %lld, step %.6Le\n", i, (long double)t.steps); }
