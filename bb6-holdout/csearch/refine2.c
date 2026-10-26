/* Exhaustive 2-adic refinement from block states  G1, B r, W R  (width w)  -- resumable, uncapped version.
   Same test as refine.c: a residue class of (r, R, w) mod 2^k is 'settled' when 3 random large completions give the
   same cascade length; unsettled classes are split into 8 at the next level.
   Changes: no cap (every unsettled class is carried on), levels kept on disk in chunks of CH classes, each chunk
   written atomically with a done marker so a killed run resumes where it stopped, 2 worker processes, and a fixed
   random seed per class so resumed runs give identical results.
   Usage: refine2 K_max dir      (prints one line per finished level; history in dir/summary.txt) */
#include "model_core.h"
#include <string.h>
#include <stdint.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <dirent.h>
#include <errno.h>
#include <signal.h>
#include <sys/prctl.h>

static ll pred(ll d) { return (d % 4 == 2) ? (d - 2) / 2 : d / 2 + 4; }
static int run_state(ll r, ll R, ll w0) {
    nm = 0; halted = 0; bad = 0; nend = 0; W = w0;
    add('G', 1); add('B', r); add('W', R);
    int L = 0;
    for (int rd = 0; rd < 400; rd++) {
        do_round();
        if (halted) return 1000;
        if (bad) return -1;
        int alive = 0, ok = 0; for (int i = 0; i < nm; i++) if (A[i]) { alive++; if (T[i] == 'M' && P[i] == W - 2) ok = 1; }
        L = nend > 0 ? 1 : 0; for (int i = 1; i < nend; i++) { if (endd[i] == pred(endd[i-1])) L++; else return L; }
        if (alive == 2 && ok) return L;
    }
    return L;
}
static uint64_t sm(uint64_t x) { x += 0x9E3779B97F4A7C15ULL; x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9ULL;
    x = (x ^ (x >> 27)) * 0x94D049BB133111EBULL; return x ^ (x >> 31); }
static const int SB = 56;
static int eval_lift(ll r0, ll R0, ll w0, int k, int t) {
    uint64_t s = sm(sm(sm((uint64_t)r0) ^ (uint64_t)R0) ^ ((uint64_t)w0 * 31 + (uint64_t)k * 7 + (uint64_t)t));
    ll M = 1LL << k;
    int top = SB - k; if (top < 6) top = 6;
    uint64_t a = sm(s), b = sm(s + 1);
    ll w = ((ll)(a >> 8) % (1LL << top) + (1LL << top)) * M + w0;
    ll D = ((ll)(b >> 8) % (1LL << (top - 2)) + (1LL << (top - 2))) * M;
    ll R = ((w - D) / M) * M + R0;
    ll r = ((w / (3 + t)) / M) * M + r0;
    return run_state(r, R, w);
}
typedef struct { ll r, R, w; } Cl;
#define CH 100000LL
#define MAXCLASSES 150000000LL   /* disk guard: 24 bytes per class */

static char *dir;
static void lvdir(char *buf, int k) { sprintf(buf, "%s/L%02d", dir, k); }
static int exists(const char *p) { struct stat st; return stat(p, &st) == 0; }

/* list the part files of a level (sorted), with class counts */
typedef struct { char name[512]; long long n; } Part;
static int cmpp(const void *a, const void *b) { return strcmp(((Part*)a)->name, ((Part*)b)->name); }
static Part *list_parts(int k, int *np, long long *tot) {
    char d[512]; lvdir(d, k); DIR *D = opendir(d); Part *ps = NULL; int n = 0, cap = 0; *tot = 0;
    struct dirent *e;
    while ((e = readdir(D))) {
        size_t l = strlen(e->d_name);
        if (l > 4 && e->d_name[0] == 'p' && !strcmp(e->d_name + l - 4, ".bin")) {
            if (n == cap) { cap = cap ? 2 * cap : 64; ps = realloc(ps, sizeof(Part) * cap); }
            snprintf(ps[n].name, 512, "%s/%s", d, e->d_name);
            struct stat st; stat(ps[n].name, &st); ps[n].n = st.st_size / (long long)sizeof(Cl); *tot += ps[n].n; n++;
        }
    }
    closedir(D); qsort(ps, n, sizeof(Part), cmpp); *np = n; return ps;
}
/* read classes [lo, hi) of the virtual concatenation of parts */
static long long read_slice(Part *ps, int np, long long lo, long long hi, Cl *out) {
    long long off = 0, got = 0;
    for (int i = 0; i < np && off < hi; off += ps[i].n, i++) {
        long long a = lo > off ? lo : off, b = hi < off + ps[i].n ? hi : off + ps[i].n;
        if (a >= b) continue;
        FILE *f = fopen(ps[i].name, "rb"); fseeko(f, (a - off) * (long long)sizeof(Cl), SEEK_SET);
        got += fread(out + got, sizeof(Cl), b - a, f); fclose(f);
    }
    return got;
}
/* process one task: lift classes [lo,hi) of level k (k digits) to k+1 digits */
static void do_task(Part *ps, int np, int k, long long t, long long lo, long long hi) {
    char od[512], pb[600], hb[600], tmp[620]; lvdir(od, k + 1);
    sprintf(hb, "%s/h%06lld.txt", od, t);
    if (exists(hb)) return;
    Cl *in = malloc(sizeof(Cl) * (hi - lo)); long long n = read_slice(ps, np, lo, hi, in);
    sprintf(pb, "%s/p%06lld.bin", od, t); sprintf(tmp, "%s.%d.tmp", pb, (int)getpid());
    FILE *f = fopen(tmp, "wb"); long long hist[64] = {0}, unsettled = 0, settled = 0; int smax = 0;
    ll M = 1LL << k;
    for (long long i = 0; i < n; i++) for (int c = 0; c < 8; c++) {
        Cl s = in[i]; s.r += (c & 1) ? M : 0; s.R += (c & 2) ? M : 0; s.w += (c & 4) ? M : 0;
        int a = eval_lift(s.r, s.R, s.w, k + 1, 0), b = eval_lift(s.r, s.R, s.w, k + 1, 1);
        int same = (a == b) && (a == eval_lift(s.r, s.R, s.w, k + 1, 2));
        if (same) { settled++; if (a >= 0 && a < 64) hist[a]++; if (a > smax) smax = a; }
        else { fwrite(&s, sizeof(Cl), 1, f); unsettled++; }
    }
    fclose(f); rename(tmp, pb); free(in);
    sprintf(tmp, "%s.%d.tmp", hb, (int)getpid()); FILE *h = fopen(tmp, "w");
    fprintf(h, "%lld %lld %d", settled, unsettled, smax); for (int i = 0; i < 64; i++) fprintf(h, " %lld", hist[i]); fprintf(h, "\n");
    fclose(h); rename(tmp, hb);
}
static void rmlevel(int k) {
    char d[512]; lvdir(d, k); DIR *D = opendir(d); if (!D) return; struct dirent *e; char p[800];
    while ((e = readdir(D))) if (e->d_name[0] != '.') { snprintf(p, 800, "%s/%s", d, e->d_name); unlink(p); }
    closedir(D); rmdir(d);
}
int main(int argc, char **argv) {
    int K = atoi(argv[1]); dir = argv[2]; mkdir(dir, 0755);
    char d[512], p[600];
    /* resume from the deepest level that has a DONE marker (earlier levels are deleted as we go) */
    int k = -1;
    for (int j = 63; j >= 3 && k < 0; j--) { lvdir(d, j); sprintf(p, "%s/DONE", d); if (exists(p)) k = j; }
    if (k < 0) {
        k = 3; lvdir(d, 3); mkdir(d, 0755); sprintf(p, "%s/p000000.bin", d); FILE *f = fopen(p, "wb");
        for (ll r = 0; r < 8; r += 2) for (ll R = 1; R < 8; R += 2) for (ll w = 0; w < 8; w += 2) { Cl c = {r, R, w}; fwrite(&c, sizeof c, 1, f); }
        fclose(f); sprintf(p, "%s/DONE", d); fclose(fopen(p, "w"));
    }
    sprintf(p, "%s/summary.txt", dir); FILE *S = fopen(p, "r");
    if (S) { char line[512]; while (fgets(line, sizeof line, S)) fputs(line, stdout); fclose(S); }
    if (k > 3) printf("[resumed after level %d]\n", k + 0);
    fflush(stdout);
    for (; k < K; k++) {
        int np; long long tot; Part *ps = list_parts(k, &np, &tot);
        if (tot == 0) break;
        if (tot > MAXCLASSES) { printf("stopping before digits %d: %lld classes exceed the disk budget\n", k + 1, tot); break; }
        lvdir(d, k + 1); mkdir(d, 0755);
        { DIR *Dd = opendir(d); struct dirent *e; char q[800];
          while ((e = readdir(Dd))) { size_t l = strlen(e->d_name); if (l > 4 && !strcmp(e->d_name + l - 4, ".tmp")) { snprintf(q, 800, "%s/%s", d, e->d_name); unlink(q); } }
          closedir(Dd); }
        long long ntask = (tot + CH - 1) / CH;
        pid_t kids[2];
        for (int c = 0; c < 2; c++) {
            kids[c] = fork();
            if (kids[c] == 0) { prctl(PR_SET_PDEATHSIG, SIGKILL); for (long long t = c; t < ntask; t += 2) do_task(ps, np, k, t, t * CH, (t + 1) * CH < tot ? (t + 1) * CH : tot); _exit(0); }
        }
        for (int c = 0; c < 2; c++) waitpid(kids[c], NULL, 0);
        /* aggregate */
        long long settled = 0, unsettled = 0, hist[64] = {0}; int smax = 0, missing = 0;
        for (long long t = 0; t < ntask; t++) {
            sprintf(p, "%s/h%06lld.txt", d, t); FILE *h = fopen(p, "r"); if (!h) { missing++; continue; }
            long long a, b; int m; if (fscanf(h, "%lld %lld %d", &a, &b, &m) != 3) { missing++; fclose(h); continue; }
            settled += a; unsettled += b; if (m > smax) smax = m;
            for (int i = 0; i < 64; i++) { long long x; if (fscanf(h, "%lld", &x) == 1) hist[i] += x; }
            fclose(h);
        }
        if (missing) { fprintf(stderr, "level %d: %d tasks missing\n", k + 1, missing); return 1; }
        /* cumulative max from the previous summary line */
        static int cmax = -1;
        if (cmax < 0) { cmax = 0; sprintf(p, "%s/cummax.txt", dir); FILE *c = fopen(p, "r"); if (c) { if (fscanf(c, "%d", &cmax) != 1) cmax = 0; fclose(c); } }
        if (smax > cmax) cmax = smax;
        sprintf(p, "%s/cummax.txt", dir); FILE *c = fopen(p, "w"); fprintf(c, "%d\n", cmax); fclose(c);
        char line[1024]; int o = sprintf(line, "digits %2d: classes lifted %lld, settled %lld (max here %d, so far %d), unsettled carried on %lld; settled lengths:",
                                         k + 1, tot * 8, settled, smax, cmax, unsettled);
        for (int i = 0; i < 64; i++) if (hist[i]) o += sprintf(line + o, " %d:%lld", i, hist[i]);
        sprintf(line + o, "\n");
        sprintf(p, "%s/summary.txt", dir); S = fopen(p, "a"); fputs(line, S); fclose(S);
        fputs(line, stdout); fflush(stdout);
        sprintf(p, "%s/DONE", d); fclose(fopen(p, "w"));
        free(ps); rmlevel(k);
    }
    return 0;
}
