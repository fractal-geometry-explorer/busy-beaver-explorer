/* ngramcps.c: the n-gram Closed Position Set decider (NGramCPS, Algorithm 2 of the Coq-BB5 paper, arXiv 2509.12337,
 * Section 4.4), for any two-symbol machine, with separate window widths on the two sides of the head and the paper's
 * two tape-alphabet augmentations (Section 4.4.2).
 *
 *   ngramcps MACHINE NL [NR] [-H LEN | -U] [-m MAXCONF] [-w FILE] [-s STEPS]
 *
 * A local configuration is (state, head symbol, the NL cells left of the head, the NR cells right of it).  Starting
 * from the blank one, the decider closes the set of local configurations under the machine's steps: a step to the
 * right shifts the left window (its farthest cell is forgotten, and the whole old left window is recorded as a "seen
 * left n-gram"); the cell that comes into view at the far end of the right window is unknown, so every seen right
 * n-gram that agrees with the NR - 1 known cells is tried.  Steps to the left are the mirror image.  If the set closes
 * without a halting local configuration, the machine never halts from blank tape (Theorem 4.6 of the paper); if a
 * halting one is reached the decider fails (UNKNOWN).
 *
 * The paper's loop ("revisit every configuration until nothing changes") is replaced by an equivalent worklist: a
 * step that needs an n-gram with given NR - 1 known cells is stored as waiting on that key, and is completed with every
 * n-gram that has the key, now and whenever a new one is recorded.  The closure is the same set (tested against a
 * literal transcription of Algorithm 2, tools/py/bbtools/ngramcps.py); configurations are processed in breadth-first
 * order, so the first halting configuration found has a short derivation.
 *
 * Augmentations (the cells carry more than their bit; the zero symbol is "0, no history"):
 *   -H LEN   fixed-length history: each cell also holds the last LEN (state, bit) pairs read there, newest first
 *   -U       Least Recent Usage history: each cell holds every (state, bit) pair read there, most recent first
 *
 * Output (stdout, one "key value" per line): result NONHALT / UNKNOWN / LIMIT, the sizes of the sets, the time and
 * the peak memory.  With -w FILE, on UNKNOWN, the derivation of the halting local configuration: the chain of local
 * configurations from the blank one, one step apart, and for each step the n-gram that was glued in at the far end of
 * a window, with the configuration that first recorded it.  With -s STEPS the (augmented) machine is also run directly
 * from blank tape for STEPS steps, and every configuration of the derivation is marked real (it occurs in that run) or
 * not; the first unreal one is where the abstraction left the machine's behaviour (as far as STEPS steps show).
 *
 *   -m MAXCONF   stop with LIMIT after this many local configurations (default 400,000,000)
 *
 * Windows are stored near cell first on both sides, so the two sides are handled by the same code; printed, the left
 * window is written far cell first (as it sits on the tape).  Augmented symbols print as their bit.
 */
#include "tm.h"
#include <time.h>
#include <sys/resource.h>

typedef unsigned long long u64;
typedef unsigned short sym;

/* ---- open-addressing hash map u64 -> u32 ---- */
typedef struct { u64 *k; unsigned *v; size_t cap, n; } hmap;
#define EMPTY (~0ULL)
static void *xmalloc(size_t n) { void *p = malloc(n); if (!p) { fprintf(stderr, "out of memory\n"); exit(2); } return p; }
static void hm_init(hmap *h, size_t cap) {
    h->cap = cap; h->n = 0; h->k = xmalloc(cap * sizeof(u64)); h->v = xmalloc(cap * sizeof(unsigned));
    memset(h->k, 0xff, cap * sizeof(u64));
}
static inline u64 mix(u64 x) { x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33; return x; }
static unsigned *hm_slot(hmap *h, u64 key, int *found);
static void hm_grow(hmap *h) {
    hmap g; hm_init(&g, h->cap * 2);
    for (size_t i = 0; i < h->cap; i++) if (h->k[i] != EMPTY) { int f; *hm_slot(&g, h->k[i], &f) = h->v[i]; }
    free(h->k); free(h->v); *h = g;
}
static unsigned *hm_slot(hmap *h, u64 key, int *found) {
    if (2 * (h->n + 1) > h->cap) hm_grow(h);
    size_t i = mix(key) & (h->cap - 1);
    while (h->k[i] != EMPTY) { if (h->k[i] == key) { *found = 1; return &h->v[i]; } i = (i + 1) & (h->cap - 1); }
    h->k[i] = key; h->n++; *found = 0; return &h->v[i];
}
static int hm_get(const hmap *h, u64 key, unsigned *val) {
    size_t i = mix(key) & (h->cap - 1);
    while (h->k[i] != EMPTY) { if (h->k[i] == key) { if (val) *val = h->v[i]; return 1; } i = (i + 1) & (h->cap - 1); }
    return 0;
}

/* ---- growable arrays ---- */
#define VEC(T) struct { T *a; size_t n, cap; }
#define RESERVE(v, k) do { while ((v).n + (k) > (v).cap) { (v).cap = (v).cap ? 2 * (v).cap : 1024; \
    (v).a = realloc((v).a, (v).cap * sizeof(*(v).a)); if (!(v).a) { fprintf(stderr, "out of memory\n"); exit(2); } } } while (0)
#define PUSH(v, x) do { RESERVE(v, 1); (v).a[(v).n++] = (x); } while (0)

/* ---- interned words of symbols (n-grams and their keys), one table per length ---- */
typedef struct { int len; VEC(sym) cells; hmap index; } words;   /* word i is cells[i*len .. i*len+len) */
static u64 whash(const sym *w, int len) { u64 h = 0x9e3779b97f4a7c15ULL; for (int i = 0; i < len; i++) h = mix(h ^ (w[i] + 1)); return h; }
static void words_init(words *t, int len) { t->len = len; t->cells.a = NULL; t->cells.n = t->cells.cap = 0; hm_init(&t->index, 1 << 10); }
/* the index maps a hash to the first word with it; collisions are chained through `wchain` */
typedef struct { VEC(int) chain; } wchainv;
static int intern(words *t, wchainv *ch, const sym *w, int *isnew) {
    u64 h = whash(w, t->len); int f; unsigned *slot = hm_slot(&t->index, h, &f);
    if (f) {
        for (int i = (int)*slot; i >= 0; i = ch->chain.a[i])
            if (!memcmp(t->cells.a + (size_t)i * t->len, w, t->len * sizeof(sym))) { *isnew = 0; return i; }
    }
    int id = (int)ch->chain.n;
    RESERVE(t->cells, (size_t)t->len); memcpy(t->cells.a + t->cells.n, w, t->len * sizeof(sym)); t->cells.n += t->len;
    PUSH(ch->chain, f ? (int)*slot : -1); *slot = (unsigned)id; *isnew = 1; return id;
}
static const sym *word(const words *t, int i) { return t->cells.a + (size_t)i * t->len; }

/* ---- augmented symbols ---- */
static tm_machine M;
static int HIST = 0, LRU = 0;          /* history length (0: plain bits), or LRU */
#define MAXH 24
#define SYMBITS 14                     /* at most 16,384 augmented symbols */
#define IDBITS 23                      /* at most 8,388,608 n-grams per side */
static int sim_mode = 0;
typedef struct { int bit, len; unsigned char h[MAXH]; } asym; /* h[i] = state * 2 + bit, newest first */
static VEC(asym) syms; static hmap symidx; static VEC(int) symchain;
static u64 shash(const asym *a) { u64 x = mix((u64)a->bit * 977 + a->len); for (int i = 0; i < a->len; i++) x = mix(x ^ (a->h[i] + 7)); return x; }
static int sym_intern(const asym *a) {
    u64 h = shash(a); int f; unsigned *slot = hm_slot(&symidx, h, &f);
    if (!f && syms.n >= (1u << SYMBITS)) {   /* full: the direct run stops there; the decider gives up */
        symidx.n--; symidx.k[slot - symidx.v] = EMPTY;   /* (just inserted at the end of its probe run) */
        if (sim_mode) return -1;
        fprintf(stderr, "more than %d augmented symbols\n", 1 << SYMBITS); exit(3);
    }
    if (f) for (int i = (int)*slot; i >= 0; i = symchain.a[i]) {
        const asym *b = &syms.a[i];
        if (b->bit == a->bit && b->len == a->len && !memcmp(b->h, a->h, a->len)) return i;
    }
    int id = (int)syms.n; PUSH(syms, *a); PUSH(symchain, f ? (int)*slot : -1); *slot = (unsigned)id;
    return id;
}
/* the symbol left on a cell holding `a` after state s reads it and writes w */
static VEC(int) wcache;   /* (a * 16 + s) * 2 + w -> id + 1 */
static int written(int a, int s, int w) {
    size_t i = ((size_t)a * 16 + s) * 2 + w;
    if (i < wcache.n && wcache.a[i]) return wcache.a[i] - 1;
    asym b = syms.a[a], c; c.bit = w; c.len = 0;
    unsigned char p = (unsigned char)(s * 2 + b.bit);
    if (HIST > 0) { c.h[c.len++] = p; for (int k = 0; k < b.len && c.len < HIST; k++) c.h[c.len++] = b.h[k]; }
    else if (LRU) { c.h[c.len++] = p; for (int k = 0; k < b.len; k++) if (b.h[k] != p) c.h[c.len++] = b.h[k]; }
    int id = sym_intern(&c);
    if (id < 0) return -1;
    while (wcache.n <= i) PUSH(wcache, 0);
    wcache.a[i] = id + 1;
    return id;
}

/* ---- the decider ---- */
static int NW[2];                       /* window widths: 0 = left, 1 = right */
static words G[2], K[2];                /* n-grams and keys (their NW-1 near cells) per side */
static wchainv GC[2], KC[2];
static VEC(int) gorig[2];               /* configuration whose step recorded the n-gram (-1: blank) */
static VEC(int) gkey[2];                /* key of the n-gram: the near NW-1 cells read from the far side inward... */
static VEC(int) gnext[2];               /* next n-gram with the same key */
static VEC(int) khead_g[2];             /* key -> first n-gram with it (-1) */
static VEC(int) khead_w[2];             /* key -> first waiter (-1) */
static VEC(char) gseen[2];              /* n-gram recorded as seen */

/* configuration key: state (3) | head (SYMBITS) | left id (IDBITS) | right id (IDBITS) */
static inline u64 ckey(int s, int m, int l, int r) { return (u64)s | ((u64)m << 3) | ((u64)l << (3 + SYMBITS)) | ((u64)r << (3 + SYMBITS + IDBITS)); }
static inline void cdec(u64 k, int *s, int *m, int *l, int *r) {
    *s = (int)(k & 7); *m = (int)((k >> 3) & ((1 << SYMBITS) - 1));
    *l = (int)((k >> (3 + SYMBITS)) & ((1 << IDBITS) - 1)); *r = (int)(k >> (3 + SYMBITS + IDBITS));
}
static VEC(u64) ck; static VEC(int) cpar; static VEC(int) cgram; static VEC(char) cgside;
static hmap cset;
typedef struct { int s, m, other, par, next; } waiter;
static VEC(waiter) wv;
static hmap wseen;
static VEC(int) queue; static size_t qhead;
static long long maxconf = 400000000LL;

static void check_id(int id) { if (id >= (1 << IDBITS)) { fprintf(stderr, "too many n-grams\n"); exit(3); } }

static int gram_id(int side, const sym *w) {
    int isnew; int id = intern(&G[side], &GC[side], w, &isnew);
    if (isnew) {
        check_id(id);
        int kn; int k = intern(&K[side], &KC[side], w, &kn);   /* key: the near NW-1 cells */
        if (kn) { PUSH(khead_g[side], -1); PUSH(khead_w[side], -1); }
        PUSH(gkey[side], k); PUSH(gnext[side], -1); PUSH(gorig[side], -1); PUSH(gseen[side], 0);
    }
    return id;
}
static int key_id(int side, const sym *w) {   /* w has NW-1 cells */
    int kn; int k = intern(&K[side], &KC[side], w, &kn);
    if (kn) { PUSH(khead_g[side], -1); PUSH(khead_w[side], -1); }
    return k;
}

static void add_conf(int s, int m, int l, int r, int par, int gram, int side) {
    u64 k = ckey(s, m, l, r); int f;
    unsigned *slot = hm_slot(&cset, k, &f);
    if (f) return;
    *slot = (unsigned)ck.n;
    PUSH(ck, k); PUSH(cpar, par); PUSH(cgram, gram); PUSH(cgside, (char)side); PUSH(queue, (int)(ck.n - 1));
}
static void complete(int side, const waiter *w, int g) {
    if (side == 1) add_conf(w->s, w->m, w->other, g, w->par, g, 1);
    else add_conf(w->s, w->m, g, w->other, w->par, g, 0);
}
static void see_gram(int side, int g, int orig) {
    if (gseen[side].a[g]) return;
    gseen[side].a[g] = 1; gorig[side].a[g] = orig;
    int k = gkey[side].a[g];
    gnext[side].a[g] = khead_g[side].a[k]; khead_g[side].a[k] = g;
    for (int i = khead_w[side].a[k]; i >= 0; i = wv.a[i].next) { waiter w = wv.a[i]; complete(side, &w, g); }
}
static void add_waiter(int side, int s, int m, int other, int k, int par) {
    u64 dk = (u64)side | ((u64)s << 1) | ((u64)m << 4) | ((u64)other << (4 + SYMBITS)) | ((u64)k << (4 + SYMBITS + IDBITS));
    if (k < (1 << (64 - 4 - SYMBITS - IDBITS))) { int f; hm_slot(&wseen, dk, &f); if (f) return; }  /* exact dedup */
    waiter w = { s, m, other, par, khead_w[side].a[k] };
    khead_w[side].a[k] = (int)wv.n; PUSH(wv, w);
    for (int g = khead_g[side].a[k]; g >= 0; g = gnext[side].a[g]) complete(side, &w, g);
}

static void wprint(char *buf, int side, int g) {
    int n = NW[side]; const sym *w = word(&G[side], g);
    for (int i = 0; i < n; i++) buf[i] = '0' + syms.a[w[side == 0 ? n - 1 - i : i]].bit;
    buf[n] = 0;
}
static void cstr(char *buf, u64 k) {
    int s, m, l, r; cdec(k, &s, &m, &l, &r);
    char a[200], b[200]; wprint(a, 0, l); wprint(b, 1, r);
    sprintf(buf, "%s %c%d %s", a, 'A' + s, syms.a[m].bit, b);
}
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: ngramcps MACHINE NL [NR] [-H LEN | -U] [-m MAXCONF] [-w FILE] [-s STEPS]\n"); return 1; }
    if (tm_parse(argv[1], &M) || M.n > 8) { fprintf(stderr, "bad machine (at most 8 states)\n"); return 1; }
    NW[0] = NW[1] = atoi(argv[2]);
    int ai = 3;
    if (argc > 3 && argv[3][0] != '-') { NW[1] = atoi(argv[3]); ai = 4; }
    const char *wfile = NULL; long long simsteps = 0;
    for (; ai < argc; ai++) {
        if (!strcmp(argv[ai], "-m") && ai + 1 < argc) maxconf = atoll(argv[++ai]);
        else if (!strcmp(argv[ai], "-w") && ai + 1 < argc) wfile = argv[++ai];
        else if (!strcmp(argv[ai], "-s") && ai + 1 < argc) simsteps = atoll(argv[++ai]);
        else if (!strcmp(argv[ai], "-H") && ai + 1 < argc) HIST = atoi(argv[++ai]);
        else if (!strcmp(argv[ai], "-U")) LRU = 1;
        else { fprintf(stderr, "unknown option %s\n", argv[ai]); return 1; }
    }
    if (NW[0] < 1 || NW[1] < 1 || NW[0] > 190 || NW[1] > 190) { fprintf(stderr, "need 1 <= NL, NR <= 190\n"); return 1; }
    if (HIST < 0 || HIST > MAXH || (LRU && 2 * M.n > MAXH)) { fprintf(stderr, "history too long\n"); return 1; }

    double t0 = now();
    hm_init(&symidx, 1 << 8);
    asym zero = { 0, 0, {0} }; sym_intern(&zero);
    hm_init(&cset, 1 << 16); hm_init(&wseen, 1 << 16);
    for (int i = 0; i < 2; i++) { words_init(&G[i], NW[i]); words_init(&K[i], NW[i] - 1); }
    sym zw[200] = {0};
    for (int i = 0; i < 2; i++) { int g = gram_id(i, zw); see_gram(i, g, -1); }
    add_conf(0, 0, 0, 0, -1, -1, 0);

    int halt = -1; const char *result = "NONHALT";
    sym nw[200];
    while (qhead < queue.n) {
        int ci = queue.a[qhead++];
        int s, m, l, r; cdec(ck.a[ci], &s, &m, &l, &r);
        int bit = syms.a[m].bit, t = M.s[s][bit];
        if (t < 0) { halt = ci; result = "UNKNOWN"; break; }
        int w = written(m, s, M.w[s][bit]);
        int side = M.d[s][bit] > 0 ? 0 : 1;   /* the side whose window grows by the written cell */
        int lw = side == 0 ? l : r, rw = side == 0 ? r : l;   /* rw: the window the head moves into */
        see_gram(side, lw, ci);
        const sym *a = word(&G[side], lw), *b = word(&G[1 - side], rw);
        nw[0] = (sym)w; memcpy(nw + 1, a, (NW[side] - 1) * sizeof(sym));
        int l2 = gram_id(side, nw);
        int m2 = b[0];
        int k = key_id(1 - side, b + 1);
        add_waiter(1 - side, t, m2, l2, k, ci);
        if ((long long)ck.n > maxconf) { result = "LIMIT"; break; }
    }
    double t1 = now();
    struct rusage ru; getrusage(RUSAGE_SELF, &ru);
    printf("machine %s\nwidths %d %d\naugmentation %s\nresult %s\nconfigs %zu\nprocessed %zu\nleft_grams %zu\nright_grams %zu\nwaiters %zu\nsymbols %zu\n",
           argv[1], NW[0], NW[1], HIST ? "history" : LRU ? "lru" : "none", result, ck.n, qhead,
           G[0].cells.n / NW[0], G[1].cells.n / NW[1], wv.n, syms.n);
    if (HIST) printf("history %d\n", HIST);
    printf("seconds %.3f\nmaxrss_mb %.1f\n", t1 - t0, ru.ru_maxrss / 1024.0);
    fflush(stdout);

    if (halt >= 0) {
        VEC(int) chain = { 0 };
        for (int c = halt; c >= 0; c = cpar.a[c]) PUSH(chain, c);
        printf("derivation_length %zu\n", chain.n - 1);
        hmap real, realg[2]; int have_real = simsteps > 0;
        if (have_real) {
            hm_init(&real, 1 << 20); hm_init(&realg[0], 1 << 16); hm_init(&realg[1], 1 << 16);
            /* the augmented machine run directly; tape of symbol ids */
            long long size = 1 << 22, off = size / 2, head = 0; sym *tape = calloc((size_t)size, sizeof(sym));
            int st = 0; sym win[200]; sim_mode = 1;
            for (long long kk = 0; kk <= simsteps; kk++) {
                if (head + off - 200 < 0 || head + off + 200 >= size) {
                    sym *t2 = calloc((size_t)(3 * size), sizeof(sym)); memcpy(t2 + size, tape, size * sizeof(sym));
                    free(tape); tape = t2; off += size; size *= 3;
                }
                int ids[2], ok = 1;
                for (int sd = 0; sd < 2 && ok; sd++) {
                    for (int i = 0; i < NW[sd]; i++) win[i] = tape[head + off + (sd ? 1 + i : -1 - i)];
                    unsigned v; ids[sd] = -1;
                    if (hm_get(&G[sd].index, whash(win, NW[sd]), &v))
                        for (int i = (int)v; i >= 0; i = GC[sd].chain.a[i])
                            if (!memcmp(word(&G[sd], i), win, NW[sd] * sizeof(sym))) { ids[sd] = i; break; }
                    if (ids[sd] < 0) ok = 0; else { int f; hm_slot(&realg[sd], (u64)ids[sd], &f); }
                }
                sym cur = tape[head + off];
                if (ok) { int f; hm_slot(&real, ckey(st, cur, ids[0], ids[1]), &f); }
                if (kk == simsteps) break;
                int bit = syms.a[cur].bit, t = M.s[st][bit];
                if (t < 0) break;
                int nwr = written(cur, st, M.w[st][bit]);
                if (nwr < 0) { printf("direct_run_stopped_at %lld (symbol table full)\n", kk); break; }
                tape[head + off] = (sym)nwr;
                head += M.d[st][bit]; st = t;
            }
            free(tape);
            printf("real_configs_known %zu\nreal_left_grams %zu\nreal_right_grams %zu\n", real.n, realg[0].n, realg[1].n);
        }
        long first_unreal = -1;
        if (have_real)
            for (long i = (long)chain.n - 1; i >= 0; i--)
                if (!hm_get(&real, ck.a[chain.a[i]], NULL)) { first_unreal = (long)chain.n - 1 - i; break; }
        if (have_real) printf("first_unreal_step %ld\n", first_unreal);
        if (wfile) {
            FILE *f = fopen(wfile, "w");
            fprintf(f, "# NGramCPS derivation of a halt: %s, widths %d %d, augmentation %s %d\n", argv[1], NW[0], NW[1],
                    HIST ? "history" : LRU ? "lru" : "none", HIST);
            fprintf(f, "# step  left window (far..near) STATE+head right window (near..far)  [real]  glued n-gram, the configuration that recorded it\n");
            for (long i = (long)chain.n - 1; i >= 0; i--) {
                int c = chain.a[i]; char buf[600]; cstr(buf, ck.a[c]);
                fprintf(f, "%6ld  %s", (long)chain.n - 1 - i, buf);
                if (have_real) fprintf(f, "  %s", hm_get(&real, ck.a[c], NULL) ? "real" : "UNREAL");
                if (cgram.a[c] >= 0) {
                    int sd = cgside.a[c], g = cgram.a[c]; char gb[200]; wprint(gb, sd, g);
                    fprintf(f, "  glued %s %s", sd ? "R" : "L", gb);
                    if (have_real) fprintf(f, " (%s)", hm_get(&realg[sd], (u64)g, NULL) ? "real n-gram" : "UNREAL n-gram");
                    if (gorig[sd].a[g] >= 0) { char ob[600]; cstr(ob, ck.a[gorig[sd].a[g]]); fprintf(f, " from #%d: %s", gorig[sd].a[g], ob); }
                    else fprintf(f, " (blank)");
                }
                fputc('\n', f);
            }
            fclose(f);
        }
    }
    return 0;
}
