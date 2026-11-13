/* items: the item-level simulator of 1RB0LD_1RC1RE_1LA0LD_1LB1LC_0RA1RF_1RA--- (see ../README.md).
 *
 * At every sweep start the head is in state D on the leftmost cell, and the tape to its right is
 *     0 (10)^n0 s0 (10)^n1 s1 ... (10)^nk sk         (s0 = 0, sk = 1: the tape ends with a 1)
 * an item list (n_i, s_i).  One sweep is the parity-signal rule (X: decrement here; Y: pass), with the special sweeps
 * reset / merge / xend / yend; any other special sweep stops the run (exit 2) and prints the items, so that it can be
 * run cell by cell (py/items.py does that).  The rules and step counts were checked against a direct simulation, see
 * py/items.py check.
 *
 *   items SWEEPS [REPORT_EVERY]        starts from the first sweep start (step 15: D> 0 0 (10)^2 0, then (2,0),(3,1))
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXI 4096
typedef long long ll;
typedef __int128 i128;
static ll n[MAXI]; static int s[MAXI]; static int L;
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

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: items SWEEPS [REPORT_EVERY]\n"); return 1; }
    ll maxs = (ll)atof(argv[1]); ll every = argc > 2 ? (ll)atof(argv[2]) : 0;
    /* the sweep start after the first (cell-level) sweep: step 55, items (2,0),(3,1) */
    L = 2; n[0] = 2; s[0] = 0; n[1] = 3; s[1] = 1;
    i128 T = 55; ll sw = 1;
    ll cnt[5] = {0};
    while (sw < maxs) {
        const char *kind = "";
        /* save for an unmodelled sweep */
        static ll sn[MAXI]; static int ss[MAXI]; int sL = L;
        memcpy(sn, n, L * sizeof(ll)); memcpy(ss, s, L * sizeof(int));
        i128 st = sweep(&kind);
        if (st < 0) {
            memcpy(n, sn, sL * sizeof(ll)); memcpy(s, ss, sL * sizeof(int)); L = sL;
            printf("UNMODELLED sweep %lld step ", sw); print128(stdout, T); printf("\n"); print_items(stdout);
            return 2;
        }
        if (strcmp(kind, "reg")) {
            cnt[kind[0] == 'r' ? 1 : kind[0] == 'm' ? 2 : kind[0] == 'x' ? 3 : 4]++;
            if (every < 0) { printf("%s %lld ", kind, sw); print128(stdout, T); printf(" "); print_items(stdout); }
        }
        T += st; sw++;
        if (every > 0 && sw % every == 0) {
            printf("AT sweep %lld step ", sw); print128(stdout, T); printf(" (%.4e) items %d: ", (double)T, L); print_items(stdout);
            fflush(stdout);
        }
    }
    printf("END sweep %lld step ", sw); print128(stdout, T);
    printf(" (%.4e) resets %lld merges %lld xends %lld yends %lld items %d\n", (double)T, cnt[1], cnt[2], cnt[3], cnt[4], L);
    print_items(stdout);
    return 0;
}
