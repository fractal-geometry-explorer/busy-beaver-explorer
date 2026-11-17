/* items_pair: the item model of 1RB0LD_1RC1RE_1LA0LD_1LB1LC_0RA1RF_1RA--- (items.c) run twice in step, to follow the
 * coupling of lean/Insert_1RB0RE1LC0RE1.lean (GoodPair) far beyond a cell-level check.
 *
 * Run A is the machine from blank tape (state A); run B is the same table from blank tape in state C, which is the
 * partner 1RB0RE_1LC0RE_1LA1LD_0LB1LF_1RC1RA_1LB--- mirrored.  Their first item lists are [(2,0),(3,1)] (step 55) and
 * [(2,0),(5,1)] (step 74); after every sweep the program checks that B's tape is A's with four cells inserted:
 * first cheaply (the lists are equal except one item that is 2 longer), else by writing out both tapes after their
 * common leading items.  It prints every change of where the extra length sits, and stops at the first sweep where
 * B is not A plus four cells (the coupling has failed), at an unmodelled sweep, or when the two tapes are too long to
 * write out (it then counts the items whose separators differ: two or more mean more than four inserted cells).
 *
 *   gcc -O2 -o items_pair items_pair.c && ./items_pair SWEEPS
 *
 * The sweep rules below are those of items.c unchanged.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXI 4096
typedef long long ll;
typedef __int128 i128;
typedef struct { ll n[MAXI]; int s[MAXI]; int L; } IL;
static IL *cur;
#define n (cur->n)
#define s (cur->s)
#define L (cur->L)

static ll cn[MAXI]; static int cs[MAXI]; /* scratch */

static void print_items(FILE *f) {
    fprintf(f, "[");
    for (int i = 0; i < L; i++) fprintf(f, "%s(%lld,%d)", i ? ", " : "", n[i], s[i]);
    fprintf(f, "]\n");
}
static void print128(FILE *f, i128 x) {
    char buf[64]; int k = 0;
    if (x == 0) { fputc('0', f); return; }
    while (x > 0) { buf[k++] = '0' + (int)(x % 10); x /= 10; }
    while (k) fputc(buf[--k], f);
}

/* one sweep; returns the step count, or -1 for an unmodelled sweep (items unchanged) */
static i128 sweep(const char **kind) {
    int sig = (n[0] % 2 == 0) ? 0 : 1;   /* 0 = X, 1 = Y */
    i128 cross = 0; int ones = 0;         /* 3 * sum(2n+1) over crossed items; sep-1 bonus */
    ll pend = -1; int pendi = -1;         /* a pending change on item i+1 (Y at even sep-1 item) */
    int changed_prefix = 0;
    ll orig_prev = n[0], orig_next = -1;  /* original lengths (the step counts use them) */
    for (int i = 1; i < L; i++) {
        cross += 3 * (i128)(2 * orig_prev + 1);
        orig_prev = (pendi == i) ? orig_next : n[i];
        ll ni = (pendi == i) ? pend : n[i];
        int si = s[i];
        if (sig == 0) {
            if (ni >= 1) {
                n[i] = ni - 1;
                n[0] += 3;
                *kind = "reg";
                return cross + 12 + 3 * i + ones;
            }
            if (si == 0) {
                if (changed_prefix || i + 1 >= L) return -1;
                for (int j = 0; j < i; j++) if (s[j] != 0) return -1;
                /* reset at i: (2,0), (n0,1), ..., (n_{i-1}+1, 1), items after i */
                i128 st = 28 - 3 * i + cross;
                int m = 0;
                cn[m] = 2; cs[m++] = 0;
                for (int j = 0; j < i - 1; j++) { cn[m] = n[j]; cs[m++] = 1; }
                cn[m] = n[i - 1] + 1; cs[m++] = 1;
                int k = m - 1, j = i + 1;
                if (j + 1 < L && n[j] == 0 && s[j] == 0) { cn[k] += 1 + n[j + 1]; cs[k] = s[j + 1]; j += 2; }
                for (; j < L; j++) { cn[m] = n[j]; cs[m++] = s[j]; }
                if (m >= MAXI) { fprintf(stderr, "too many items\n"); exit(3); }
                memcpy(n, cn, m * sizeof(ll)); memcpy(s, cs, m * sizeof(int)); L = m;
                *kind = "reset";
                return st;
            }
            /* X at (0,1) */
            {
                ll p = (pendi == i - 1) ? pend : n[i - 1];
                if (s[i - 1] != 0 || i < 2) return -1;
                if (i == L - 1) {
                    if (p < 1) return -1;
                    n[i - 1] = p - 1; s[i - 1] = 1; L--;
                    n[0] += 3;
                    *kind = "xend";
                    return cross + 12 + 3 * i + ones;
                }
                ll m2 = n[i + 1]; int ms = s[i + 1];
                n[i - 1] = p + m2; s[i - 1] = ms;
                memmove(n + i, n + i + 2, (L - i - 2) * sizeof(ll));
                memmove(s + i, s + i + 2, (L - i - 2) * sizeof(int));
                L -= 2;
                n[0] += 3;
                *kind = "merge";
                return cross + 12 + 3 * i + ones;
            }
        }
        if (si == 0) {
            sig = (ni % 2 == 0) ? 0 : 1;
        } else {
            if (i == L - 1) {
                if (changed_prefix) return -1;
                for (int j = 0; j < i; j++) if (s[j] != 0) return -1;
                i128 st = cross + 6 * (i128)ni + 34 - 3 * i;
                int m = 0;
                cn[m] = 2; cs[m++] = 0;
                for (int j = 0; j < i; j++) { cn[m] = n[j]; cs[m++] = 1; }
                if (ni % 2 == 1) { cn[m] = ni + 2; cs[m++] = 1; }
                else { cn[m] = ni + 1; cs[m++] = 1; cn[m] = 1; cs[m++] = 1; }
                if (m >= MAXI) { fprintf(stderr, "too many items\n"); exit(3); }
                memcpy(n, cn, m * sizeof(ll)); memcpy(s, cs, m * sizeof(int)); L = m;
                *kind = "yend";
                return st;
            }
            if (ni % 2 == 1) { s[i] = 0; ones += 2; }
            else {
                if (n[i + 1] < 1) return -1;
                n[i] = ni + 1; s[i] = 0; ones += 4;
                orig_next = n[i + 1];
                pend = n[i + 1] - 1; pendi = i + 1;
                n[i + 1] = pend;
            }
            changed_prefix = 1;
            sig = 0;
        }
    }
    return -1;
}


#undef n
#undef s
#undef L
static IL A_,B_;
static i128 sweepOn(IL*x,const char**k){cur=x;return sweep(k);}
/* classify difference: B equals A except one item with n larger by 2 */
static int diffidx(IL*a,IL*b){
  if(a->L!=b->L) return -2;
  int idx=-1;
  for(int i=0;i<a->L;i++){
    if(a->s[i]!=b->s[i]) return -3;
    if(a->n[i]!=b->n[i]){ if(idx>=0||b->n[i]!=a->n[i]+2) return -4; idx=i; }
  }
  return idx;
}

static char bufA[8000000],bufB[8000000];
static long expand(IL*x,int from,char*buf,long cap){ long k=0; for(int i=from;i<x->L;i++){ for(ll j=0;j<x->n[i];j++){ if(k+2>=cap) return -1; buf[k++]='1';buf[k++]='0'; } if(k+1>=cap) return -1; buf[k++]='0'+x->s[i]; } return k; }
static int tapeins(IL*a,IL*b){
  int i=0; while(i<a->L&&i<b->L&&a->n[i]==b->n[i]&&a->s[i]==b->s[i]) i++;
  long la=expand(a,i,bufA,sizeof bufA), lb=expand(b,i,bufB,sizeof bufB);
  if(la<0||lb<0) return -1;
  while(la>0&&bufA[la-1]=='0') la--;
  while(lb>0&&bufB[lb-1]=='0') lb--;
  if(lb<la+4) return 0;
  /* pad A with zeros to lb-4 */
  for(long k=la;k<lb-4;k++) bufA[k]='0';
  la=lb-4;
  long p=0; while(p<la&&bufA[p]==bufB[p]) p++;
  long q=0; while(q<la&&bufA[la-1-q]==bufB[lb-1-q]) q++;
  return p+q>=la;
}
static void pr(IL*x){for(int i=0;i<x->L;i++)printf("(%lld,%d)",x->n[i],x->s[i]);printf("\n");}
int main(int argc,char**argv){
  ll maxs=(ll)atof(argv[1]);
  A_.L=2;A_.n[0]=2;A_.s[0]=0;A_.n[1]=3;A_.s[1]=1;
  B_.L=2;B_.n[0]=2;B_.s[0]=0;B_.n[1]=5;B_.s[1]=1;
  i128 TA=55,TB=74; ll sw=1; int last=-99; ll nexp=0;
  while(sw<maxs){
    const char*ka="",*kb="";
    i128 sa=sweepOn(&A_,&ka); i128 sb=sweepOn(&B_,&kb);
    if(sa<0||sb<0){printf("unmodelled at sweep %lld: A %d B %d\n",sw,(int)(sa<0),(int)(sb<0));pr(&A_);pr(&B_);break;}
    TA+=sa;TB+=sb;sw++;
    int d=diffidx(&A_,&B_); int code;
    if(d>=0) code=A_.L-1-d; else { nexp++; int ti=tapeins(&A_,&B_); if(ti==-1){ int ds=0; for(int i=0;i<A_.L&&i<B_.L;i++) ds+=A_.s[i]!=B_.s[i];
        printf("TOO LONG TO WRITE OUT at sweep %lld, kinds %s/%s, stepA %.6e: %d and %d items, separators differ at %d positions\n",sw,ka,kb,(double)TA,A_.L,B_.L,ds); pr(&A_); pr(&B_); break; }
      if(ti!=1){ printf("BROKEN at sweep %lld kinds %s/%s stepA %.6e\n",sw,ka,kb,(double)TA); pr(&A_); pr(&B_); break; } code=-1000; }
    if(code!=last){ printf("sweep %lld step %.4e: %s kinds %s/%s L=%d",sw,(double)TA, code>=0?"item+2":"tape+4",ka,kb,A_.L); if(code>=0)printf(" fromEnd %d value %lld",code,A_.n[d]); printf("\n"); last=code; }
  }
  printf("end sweep %lld stepA %.4e expensive %lld\n",sw,(double)TA,nexp); pr(&A_); pr(&B_);
}
