/* blockrun: iterate a block map (the table printed by `py/blockmap.py export`) from blank tape.
 *
 *   python3 holdouts/MACHINE/py/blockmap.py export > /tmp/table.txt
 *   gcc -O2 -o blockrun holdouts/MACHINE/c/blockrun.c && ./blockrun /tmp/table.txt MAX_FRAMES
 *
 * Prints, at each power of ten of frames and at the end: frames, machine steps (the sum of the cases' step counts;
 * exact while below 2^63, the program stops before an overflow), blocks on the tape, the longest block seen.  Stops
 * at a critical frame.  The table format, one case per line:
 *   q kl sl kr sr halt q2 nl nr  [nl+1 triples: left blocks, then the open left block]  [nr+1 triples]  steps-triple
 * kinds: 0 = exactly s, 1 = at least s (variable block), 2 = at least s (only s cells in the window); a triple
 * (k, ca, cb) is the number k + ca*a + cb*b with a = l0 - sl, b = r0 - sr. */
#include <stdio.h>
#include <stdlib.h>
typedef long long ll;
typedef struct { ll k, a, b; } lin;
typedef struct { int q, kl, kr, halt, q2, nl, nr; ll sl, sr; lin lb[16], rb[16], st; } leaf;
static leaf T[512]; static int nT, first[7];
static inline ll ev(const lin *x, ll a, ll b) { return x->k + x->a * a + x->b * b; }
int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: blockrun TABLE MAX_FRAMES\n"); return 1; }
  FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 1; }
  ll maxf = atoll(argv[2]);
  while (nT < 512) {
    leaf *l = &T[nT];
    if (fscanf(f, "%d %d %lld %d %lld %d %d %d %d", &l->q, &l->kl, &l->sl, &l->kr, &l->sr, &l->halt, &l->q2, &l->nl, &l->nr) != 9) break;
    for (int i = 0; i <= l->nl; i++) fscanf(f, "%lld %lld %lld", &l->lb[i].k, &l->lb[i].a, &l->lb[i].b);
    for (int i = 0; i <= l->nr; i++) fscanf(f, "%lld %lld %lld", &l->rb[i].k, &l->rb[i].a, &l->rb[i].b);
    fscanf(f, "%lld %lld %lld", &l->st.k, &l->st.a, &l->st.b);
    nT++;
  }
  for (int q = 0; q <= 6; q++) { first[q] = nT; for (int i = nT - 1; i >= 0; i--) if (T[i].q >= q) first[q] = i; }
  size_t cap = 1 << 26; ll *L = malloc(cap * sizeof(ll)), *R = malloc(cap * sizeof(ll)); size_t nl = 0, nr = 0;
  int q = 0; ll frames = 0, steps = 0, next = 10, longest = 0;
  for (; frames < maxf; frames++) {
    ll l0 = nl ? L[nl - 1] : 0, r0 = nr ? R[nr - 1] : 0;
    leaf *l = 0;
    for (int i = first[q]; i < first[q + 1]; i++) {
      leaf *c = &T[i];
      if ((c->kl == 0 ? l0 == c->sl : l0 >= c->sl) && (c->kr == 0 ? r0 == c->sr : r0 >= c->sr)) { l = c; break; }
    }
    if (!l) { printf("no case at frame %lld\n", frames); return 1; }
    if (l->halt) { printf("CRITICAL frame after %lld frames, %lld steps: state %c, l0 = %lld, r0 = %lld\n", frames, steps, 'A' + q, l0, r0); return 0; }
    ll a = l0 - l->sl, b = r0 - l->sr, x;
    if (nl) nl--;
    if (l->kl == 2) x = ev(&l->lb[l->nl], a, b) + a; else { x = ev(&l->lb[l->nl], a, b) + (nl ? L[nl - 1] : 0); if (nl) nl--; }
    L[nl++] = x; if (x > longest) longest = x;
    for (int i = l->nl - 1; i >= 0; i--) L[nl++] = ev(&l->lb[i], a, b);
    if (nr) nr--;
    if (l->kr == 2) x = ev(&l->rb[l->nr], a, b) + b; else { x = ev(&l->rb[l->nr], a, b) + (nr ? R[nr - 1] : 0); if (nr) nr--; }
    R[nr++] = x; if (x > longest) longest = x;
    for (int i = l->nr - 1; i >= 0; i--) R[nr++] = ev(&l->rb[i], a, b);
    if (nl + 20 > cap || nr + 20 > cap) { printf("tape too long\n"); return 1; }
    ll d = ev(&l->st, a, b);
    if (steps > 9000000000000000000LL - d) { printf("step count too large after %lld frames\n", frames); return 1; }
    steps += d; q = l->q2;
    if (frames + 1 == next) { printf("frames %lld steps %lld blocks %zu longest %lld\n", frames + 1, steps, nl + nr, longest); next *= 10; fflush(stdout); }
  }
  printf("frames %lld steps %lld blocks %zu longest %lld (no critical frame)\n", frames, steps, nl + nr, longest);
  return 0;
}
