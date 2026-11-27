// tmrun: helper for shuffle_test.py.
//   tmrun dump TM t1 t2 ...   print the configuration "q L R" after t_i steps (increasing); L = cells left of the head
//                              (far to near, from the first non-zero cell), R = head cell and the cells to its right.
//   tmrun run TM N            read configurations "q L R" from stdin, run each N steps, print halting step or -1.
#include <bits/stdc++.h>
using namespace std;
struct Tr { int w, dir, ns; bool def; } tr[8][2];
int main(int argc, char** argv) {
  string mode = argv[1], tm = argv[2]; int NS = (tm.size() + 1) / 7;
  for (int s = 0; s < NS; s++) for (int b = 0; b < 2; b++) { const char* t = tm.c_str() + s * 7 + b * 3;
    if (t[0] == '-') tr[s][b].def = false; else tr[s][b] = {t[0] - '0', t[1] == 'R' ? 1 : -1, t[2] - 'A', true}; }
  if (mode == "dump") {
    const int Lm = 1 << 24; vector<char> tape(2 * Lm, 0); int h = Lm, q = 0, lo = h, hi = h; long t = 0;
    for (int i = 3; i < argc; i++) { long T = atol(argv[i]);
      for (; t < T; t++) { const Tr& x = tr[q][(int)tape[h]]; if (!x.def) { printf("HALT %ld\n", t); return 0; } tape[h] = x.w; h += x.dir; q = x.ns; lo = min(lo, h); hi = max(hi, h); }
      int a = lo, b = hi; while (a < h && !tape[a]) a++; while (b > h && !tape[b]) b--;
      printf("%d ", q); for (int j = a; j < h; j++) putchar('0' + tape[j]); printf(" "); for (int j = h; j <= b; j++) putchar('0' + tape[j]); printf("\n"); }
  } else if (mode == "step") { // read "q L R N", print the configuration after N steps, or "HALT t"
    char* L = new char[1 << 24]; char* Rr = new char[1 << 24]; int q; long N;
    while (scanf("%d %s %s %ld", &q, L, Rr, &N) == 4) {
      string l = L, r = Rr; if (l == "-") l = ""; long span = N + 2; vector<char> tape(l.size() + r.size() + 2 * span, 0);
      long h = span + l.size(), lo = span, hi = h + (long)r.size() - 1; for (size_t j = 0; j < l.size(); j++) tape[span + j] = l[j] - '0'; for (size_t j = 0; j < r.size(); j++) tape[h + j] = r[j] - '0';
      long t; bool halted = false; for (t = 0; t < N; t++) { const Tr& x = tr[q][(int)tape[h]]; if (!x.def) { halted = true; break; } tape[h] = x.w; h += x.dir; q = x.ns; if (h < lo) lo = h; if (h > hi) hi = h; }
      if (halted) { printf("HALT %ld\n", t); continue; }
      long a = lo, b = hi; while (a < h && !tape[a]) a++; while (b > h && !tape[b]) b--;
      printf("%d ", q); if (a == h) putchar('-'); for (long j = a; j < h; j++) putchar('0' + tape[j]); printf(" "); for (long j = h; j <= b; j++) putchar('0' + tape[j]); printf("\n");
    }
  } else {
    long N = atol(argv[3]); char* L = new char[1 << 24]; char* Rr = new char[1 << 24]; int q;
    while (scanf("%d %s %s", &q, L, Rr) == 3) {
      string l = L, r = Rr; if (l == "-") l = ""; long pad = 4 * (long)sqrt((double)N) + 1000;
      // the head moves at most N cells; allocate lazily with a deque-free scheme: bounded by N
      long span = min(N, (long)50000000) + 2; vector<char> tape(l.size() + r.size() + 2 * span, 0); (void)pad;
      long h = span + l.size(); for (size_t j = 0; j < l.size(); j++) tape[span + j] = l[j] - '0'; for (size_t j = 0; j < r.size(); j++) tape[h + j] = r[j] - '0';
      long t, res = -1; for (t = 0; t < N; t++) { const Tr& x = tr[q][(int)tape[h]]; if (!x.def) { res = t; break; } tape[h] = x.w; h += x.dir; q = x.ns; }
      printf("%ld\n", res);
    }
  }
}
