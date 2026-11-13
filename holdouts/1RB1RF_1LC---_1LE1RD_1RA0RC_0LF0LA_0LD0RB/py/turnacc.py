"""Turn-sampled accelerator: rlsim.Sim (exact run-length simulation) + extrapolation of nested linear cycles.

Sample points are the *turns* of the head (a step whose direction differs from the previous one).  At a turn the
tape is re-tokenised with the given words, with a token boundary at the head.  The key of a sample is (state,
direction, word sequence, head token index).  When the last samples with one key have counts in arithmetic
progression (the same increment at least three times) and step counts whose increments are a polynomial in the
cycle index (constant D-th difference, D <= 4, seen at least twice), the cycle is applied k more times at once,
k chosen so that every decreasing count stays >= margin.  Nested loops (an inner cycle accelerated inside every outer
cycle) give outer step increments that are polynomials of higher degree: D grows by one per level.

This is an extrapolation, not a proof: it is checked against the unaccelerated simulator (`check`).
"""
import bisect, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rlsim import Sim
from genacc import canon_multi


def split_at(tok, pos):
    """Make a token boundary before absolute cell pos; return the index of the token starting at pos."""
    p = 0
    for i, (w, n) in enumerate(tok):
        L = len(w) * n
        if p == pos:
            return i
        if p < pos < p + L:
            off = pos - p
            if off % len(w) == 0:
                k = off // len(w)
                tok[i:i + 1] = [[w, k], [w, n - k]]
                return i + 1
            # split inside a copy: explode that copy
            k = off // len(w)
            r = off % len(w)
            parts = []
            if k: parts.append([w, k])
            parts += [[c, 1] for c in w]
            if n - k - 1: parts.append([w, n - k - 1])
            tok[i:i + 1] = parts
            return split_at(tok, pos)
        p += L
    return len(tok)


def diffs(v):
    return [b - a for a, b in zip(v, v[1:])]


class TurnAcc:
    def __init__(self, machine, words, margin=3, minrun=2, maxdeg=4, tokens=None, state=0, head=0, dir=1):
        self.m = machine; self.words = words; self.margin = margin; self.minrun = minrun; self.maxdeg = maxdeg
        self.s = Sim(machine, tokens or [['0', 1]], state, head); self.s.dir = dir
        self.hist = {}; self.jumps = 0; self.jumped = 0

    def head_pos(self):
        s = self.s
        p = 0
        for i in range(min(s.h, len(s.tok))):
            w, n = s.tok[i]; p += len(w) * n
        if s.h < 0:
            return -1
        if s.h >= len(s.tok):
            return p
        if s.dir == 1:
            return p
        w, n = s.tok[s.h]
        return p + len(w) * n - 1

    def sample(self):
        s = self.s
        if s.h < 0:
            s.tok.insert(0, ['0', 1]); s.h = 0
        if s.h >= len(s.tok):
            s.tok.append(['0', 1])
        pos = self.head_pos()
        tok = canon_multi(s.tok, self.words, self.minrun)
        if s.dir == 1:
            h = split_at(tok, pos)
        else:
            h = split_at(tok, pos + 1) - 1
        s.tok = tok; s.h = h
        key = (s.q, s.dir, h, tuple(w for w, n in tok))
        counts = tuple(n for w, n in tok)
        hist = self.hist.setdefault(key, [])
        hist.append((counts, s.steps)); del hist[:-(self.maxdeg + 4)]
        return self.try_jump(key, hist)

    def try_jump(self, key, hist):
        s = self.s
        if len(hist) < 4:
            return False
        c = [h[0] for h in hist]; t = [h[1] for h in hist]
        d = tuple(b - a for a, b in zip(c[-2], c[-1]))
        if not any(d):
            return False
        # how many trailing samples have this same count increment
        m = 1
        while m < len(c) and tuple(b - a for a, b in zip(c[-m - 1], c[-m])) == d:
            m += 1
        # m samples ... m-1 increments equal; use the last m samples
        if m < 4:
            return False
        tt = t[-m:]
        D1 = diffs(tt)
        deg = None
        cur = D1
        for dg in range(self.maxdeg + 1):
            if len(cur) >= 2 and all(x == cur[0] for x in cur):
                deg = dg; break
            cur = diffs(cur)
            if len(cur) < 2:
                break
        if deg is None:
            return False
        ks = [(n - self.margin) // (-dd) for n, dd in zip(c[-1], d) if dd < 0]
        if not ks:
            return False
        k = min(ks)
        if k < 2:
            return False
        # last values of the difference table of the step increments
        tab = [D1]
        for _ in range(deg):
            tab.append(diffs(tab[-1]))
        last = [row[-1] for row in tab]          # last[0] = last increment, last[j] = last j-th difference
        # future increments: inc_j = sum_i last[i] * C(j + i - 1, i) ... use explicit iteration via binomial sums
        # sum_{j=1..k} inc_j where inc_j = sum_{i=0..deg} last[i] * C(j+i-1, i)  (Newton forward from the end)
        total = 0
        for i in range(deg + 1):
            # sum_{j=1..k} C(j+i-1, i) = C(k+i, i+1)
            total += last[i] * comb(k + i, i + 1)
        s.tok = [[w, n + k * dd] for (w, n), dd in zip(s.tok, d)]
        s.steps += total
        self.jumps += 1; self.jumped += k
        hist.clear()
        return True

    def run(self, maxsteps, on_sample=None):
        s = self.s
        while s.steps < maxsteps:
            d0 = [s.dir]

            def stop(x):
                if x.dir != d0[0]:
                    return True
                return False
            r = s.run(maxsteps, stop)
            if r == 'halt':
                return 'halt'
            if r == 'max':
                return 'max'
            j = self.sample()
            if on_sample:
                on_sample(self, j)
        return 'max'


def comb(n, r):
    from math import comb as c
    return c(n, r)


def tape_str(s):
    return ''.join(w * n for w, n in s.tok).strip('0')


def check(machine, words, maxsteps):
    """Compare every sample of the accelerated run with the plain run-length simulation at the same step."""
    A = TurnAcc(machine, words)
    got = {}

    def on(a, j):
        got[a.s.steps] = (a.s.q, tape_str(a.s))
    r = A.run(maxsteps, on)
    B = Sim(machine, [['0', 1]], 0); B.s = B; B.dir = 1
    n = ok = 0
    while B.steps < maxsteps:
        d0 = B.dir
        r2 = B.run(maxsteps, lambda x: x.dir != d0)
        if r2 != 'stop':
            break
        if B.steps in got:
            n += 1
            if got[B.steps] == (B.q, tape_str(B)):
                ok += 1
            else:
                print('MISMATCH at', B.steps); return False
    print(f'{r} {A.s.steps}: {len(got)} samples, {A.jumps} jumps, compared {n}, ok {ok}')
    return True


if __name__ == '__main__':
    if sys.argv[1] == 'check':
        check(sys.argv[2], sys.argv[3].split(','), int(float(sys.argv[4])))
