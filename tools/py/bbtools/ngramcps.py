"""NGramCPS (Coq-BB5 paper, arXiv 2509.12337, Algorithm 2 and the augmentations of Section 4.4.2), written as
literally as the pseudo-code: the reference that `tools/c/ngramcps.c` (a worklist version of the same closure) is
tested against.

ngram_cps(machine, nl, nr=None, history=0, lru=False) -> ("NONHALT" | "UNKNOWN" | "LIMIT", set of local configurations)

A local configuration is (left window, state, head symbol, right window); windows are tuples of cells, the left one
far cell first, the right one near cell first, as in the paper's text (011 [B0] 100).  A cell is its bit, or with an
augmentation the pair (bit, history), the history a tuple of (state, bit) pairs read on the cell, newest first:
the last `history` of them, or with `lru` every distinct pair, most recent first.  The zero symbol is (0, ()).
"""
from .machine import Machine


def ngram_cps(machine, nl, nr=None, history=0, lru=False, limit=None):
    m = machine if isinstance(machine, Machine) else Machine.parse(machine)
    nr = nl if nr is None else nr
    aug = history > 0 or lru
    zero = (0, ()) if aug else 0

    def bit(a):
        return a[0] if aug else a

    def write(a, s, w):
        if not aug:
            return w
        p = (s, a[0])
        if lru:
            return (w, (p,) + tuple(q for q in a[1] if q != p))
        return (w, ((p,) + a[1])[:history])

    L = {(zero,) * nl}
    R = {(zero,) * nr}
    C = {((zero,) * nl, 0, zero, (zero,) * nr)}
    while True:
        V = list(C)
        any_updates = False
        while V:
            c = V.pop()
            left, s, mid, right = c
            tr = m.table[s][bit(mid)]
            if tr is None:
                return "UNKNOWN", C
            w, d, t = tr
            w = write(mid, s, w)
            if d > 0:
                L.add(left)
                l2 = left[1:] + (w,)
                for r in list(R):
                    if r[:nr - 1] == right[1:]:
                        c2 = (l2, t, right[0], r)
                        if c2 not in C:
                            C.add(c2); V.append(c2); any_updates = True
            else:
                R.add(right)
                r2 = (w,) + right[:nr - 1]
                for l in list(L):
                    if l[1:] == left[:nl - 1]:
                        c2 = (l, t, left[-1], r2)
                        if c2 not in C:
                            C.add(c2); V.append(c2); any_updates = True
            if limit and len(C) > limit:
                return "LIMIT", C
        if not any_updates:
            return "NONHALT", C
