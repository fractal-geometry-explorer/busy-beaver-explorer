"""Shifted right-end events of 1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA: the cascade, by direct simulation.

A pass of the head to the left (F and A alternating) reads the tape in pairs (A-cell, F-cell). A wall visit is the
pass turning on a blank pair. A right-end event with last digit b <= 10 sends the head home in the *other* pair
grid; there the pair at the next blank stretch is 01, not 00, and the head runs a *cascade* whose result depends
only on m, the number of blank cells left of the turning pair (lean/Cascade.lean, for every tape around it):

  m = 0  a hit in the new grid       m = 3  halt                      m >= 6  a wall visit 7 cells on
  m = 1  one more sub-visit          m = 4, 5  the pass goes on         (the frame goes on in the new grid)
  m = 2  a hit in the old grid                 to the next frame out

  python3 cascade.py words N   every word of at most N pairs, one wall visit each (N = 18: about 10 s):
                               halting <=> some cascade has m = 3; the first cascade comes exactly with a last digit
                               b <= 10 and has m = 2 * (sub-visits still to come in the innermost frame of the
                               recursion); m = 4 hands the pass to the next frame out; what follows m >= 6
  python3 cascade.py run       the cascades of the run from blank tape in its first 3,000,000 steps (events 1 to 5)
"""
import os, sys, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from events import all_words, cells, Gctx

M = "1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA"
TAB = []
for _s in M.split("_"):
    TAB.append([None if _s[3 * r] == "-" else (int(_s[3 * r]), 1 if _s[3 * r + 1] == "R" else -1, ord(_s[3 * r + 2]) - 65)
                for r in (0, 1)])
INF = 99   # a cascade with only blank tape to its left


def visit(w, cap=10 ** 7):
    """one wall visit of the word w: ('H' | 'V<offset>' | 'T', the m of every cascade in order)"""
    c = cells(w)
    t = {i + 1: int(ch) for i, ch in enumerate(c)}
    p, s, n, lo, prev, cs = 0, 5, 0, 0, None, []
    while n < cap:
        r = t.get(p, 0)
        if prev == (5, 1) and s == 0 and r == 0:          # F flipped a 1, A reads 0: a cascade
            m = 0
            while t.get(p - 1 - m, 0) == 0 and p - 1 - m >= lo - 1:
                m += 1
            cs.append(m if p - 1 - m >= lo - 1 else INF)
        tr = TAB[s][r]
        if tr is None:
            return "H", cs
        prev = (s, r)
        t[p] = tr[0]; p += tr[1]; s = tr[2]; n += 1
        if p < lo:
            lo = p
            if s == 5 and t.get(p, 0) == 0:
                return "V%d" % p, cs
    return "T", cs


def words(n):
    C = collections.Counter()
    for w in all_words(n):
        kind, cs = visit(list(w))
        r = Gctx(list(w))
        b = r[1][-1] if r[0] == "EVENT" else None
        C["words"] += 1
        C["halt"] += kind == "H"
        C["some cascade has m = 3"] += 3 in cs
        C["halt and m = 3 in the same visit"] += kind == "H" and 3 in cs
        if cs:
            C["first cascade even" if cs[0] == INF or cs[0] % 2 == 0 else "FIRST CASCADE ODD"] += 1
            C["m = 3 is the first cascade"] += cs[0] == 3
        if b is None:
            C["no event in G: no cascade" if not cs else "NO EVENT BUT A CASCADE"] += 1
            continue
        if b <= 10:
            pred = INF if not r[2] else 2 * r[2][-1][1]
            C["b <= 10: first m = 2 * (sub-visits to come)" if cs and cs[0] == pred else "b <= 10: FIRST m DIFFERS"] += 1
            if cs[0] in (4, 5):
                pred2 = INF if len(r[2]) < 2 else 2 * r[2][-2][1]
                C["m = 4: next m = 2 * (sub-visits to come in the next frame out)" if len(cs) > 1 and cs[1] == pred2
                  else "m = 4: NEXT m DIFFERS"] += 1
            elif cs[0] != INF and cs[0] >= 6:
                pred2 = INF if len(r[2]) < 2 else 2 * r[2][-2][1]
                nxt = cs[1] if len(cs) > 1 else None
                C["m >= 6, then: %s" % ("the next frame out, m = 2 * (sub-visits to come)" if nxt == pred2 else
                                        "no other cascade" if nxt is None else
                                        "an odd m (a second event in the shifted frame)" if nxt % 2 else
                                        "an even m (a second event in a deeper frame)")] += 1
        else:
            C["b >= 11 (G extended by h(b) = g(b)): cascades later or none"] += 1
    for k, v in C.items():
        print("  %-75s %d" % (k, v))


def run(steps=3 * 10 ** 6):
    t, p, s, n, prev, lo, walls = {}, 0, 0, 0, None, 0, 0
    while n < steps:
        r = t.get(p, 0)
        if s == 5 and r == 0 and p <= lo and t.get(p - 1, 0) == 0:
            walls += 1
        if prev == (5, 1) and s == 0 and r == 0:
            m = 0
            while t.get(p - 1 - m, 0) == 0 and p - 1 - m >= lo - 1:
                m += 1
            print("step %7d  after wall visit %3d  cascade m = %s" % (n, walls, m if p - 1 - m >= lo - 1 else "inf"))
        tr = TAB[s][r]
        if tr is None:
            print("halt"); return
        prev = (s, r)
        t[p] = tr[0]; p += tr[1]; s = tr[2]; n += 1
        lo = min(lo, p)


if __name__ == "__main__":
    if sys.argv[1] == "words":
        words(int(sys.argv[2]))
    else:
        run()
