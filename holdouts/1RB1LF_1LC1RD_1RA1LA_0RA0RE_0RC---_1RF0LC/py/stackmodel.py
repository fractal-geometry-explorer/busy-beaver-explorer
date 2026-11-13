"""The wall of 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC as a stack of counters: a model fitted by hand and compared
with zonemap.py (the step map that lean/Zone.lean proves faithful).  Observed, not proved.

A step start is  W A> 0 b^N 1  (b = 110).  Every wall met is  W = 1 X_1 ... X_n  with items
    K(k)  = b^k 1^3 b 1        (an open counter)          K'(k) = b^k 1^6       (a closed counter)      k >= 0
(the walls 1^(3j+1) and 1^(3j+1) b 1 of the first analysis are 1 K'(0)^(j/2) and 1 K'(0)^((j-1)/2) K(0)).
A step sends a *signal* (a parity) into the wall from the right and the wall answers with an amount o of copies of b:

    step(1, 0)        = (1, 2)                     step(1, 1)        = (1 K(0), 0)
    step(V K(k), 0)   = (V K'(k), 2)
    (see `step` below for the exact amounts, which come in two kinds)

and the block:  N' = 3N/2 + 5 + o (N even),  (3N + 9)/2 + o (N odd),  with (W', o) = step(W, N mod 2).
The model is only claimed while every new count stays >= 0 and N is large; it has no halting rule, and it does not
cover a closed counter K'(0) lying under other items (really one closed counter with a longer run of 1s).

usage:
  python3 stackmodel.py orbit STEPS         compare with zonemap.step_map along the orbit from step 10,206
  python3 stackmodel.py random CASES [SEED] compare on random walls of up to 5 items, both parities of N
"""
import os, sys, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zonemap as Z

b = '110'
def word(lv):
    return '1' + ''.join(b * k + ('111111' if pr else '111' + b + '1') for k, pr in lv)
def unword(s):
    if not s.startswith('1'): return None
    rest = s[1:]; lv = []
    while rest:
        k = 0
        while rest.startswith(b): k += 1; rest = rest[3:]
        if rest.startswith('111' + b + '1'): lv.append((k, False)); rest = rest[7:]
        elif rest.startswith('111111'): lv.append((k, True)); rest = rest[6:]
        else: return None
    return lv
def step(lv, s):
    """-> (lv', om, orr) or None when a count would go negative.  om: what the item below adds to its count;
    orr: the same amount before the 3/2 gain of closed counters that were dissolved (what the item below passes on)."""
    if not lv:
        return ([], 2, 2) if s == 0 else ([(0, False)], 0, 0)
    k, pr = lv[-1]; V = lv[:-1]
    if not pr:
        if s == 0: return (V + [(k, True)], 2, 2)
        r = step(V, k % 2)
        if r is None: return None
        k2 = 3 * k // 2 + r[1]
        if k2 < 0: return None
        o = -(k2 - k) + r[2]
        return (r[0] + [(k2, False)], o, o)
    if k == 0 and s == 1: return (V + [(0, True), (0, False)], 0, 0)
    r = step(V, (k + s) % 2)
    if r is None: return None
    c = 2 + s * (1 + k % 2)
    return (r[0], r[1] + 3 * k // 2 + c, r[2] + k + 2)
def stepN(lv, N):
    r = step(lv, N % 2)
    if r is None: return None
    N2 = (3 * N // 2 + 5 if N % 2 == 0 else (3 * N + 9) // 2) + r[1]
    return None if N2 < 0 else (r[0], N2)


def orbit(steps):
    W, N = Z.START
    bad = maxlev = outside = 0; first = None
    for i in range(steps):
        lv = unword(Z.show(W))
        r = Z.step_map(W, N)
        if len(r) != 2:
            print('the step map stops:', r[0], 'at orbit step', i); return
        if lv is None:
            outside += 1
        else:
            maxlev = max(maxlev, len(lv))
            m = stepN(lv, N)
            if m is None or word(m[0]) != Z.show(r[0]) or m[1] != r[1]:
                bad += 1
                if first is None: first = (i, lv, N % 2)
        W, N = r
    print(f"{steps} orbit steps: {outside} walls outside the grammar, model differs from the step map in {bad}, "
          f"at most {maxlev} items in a wall, N has {N.bit_length()} bits")
    if first: print('first difference:', first)


def rand(cases, seed=1):
    tow = lambda s: tuple(int(c) for c in reversed(s))
    random.seed(seed)
    n = bad = skipped = under = 0
    for t in range(cases):
        L = random.randint(0, 5)
        lv = [(random.choice([0, 0, 1, 2, 3]) if random.random() < 0.3 else random.randint(0, 40), random.random() < 0.35)
              for _ in range(L)]
        buried = any(k == 0 and pr for k, pr in lv[:-1]) or (len(lv) > 1 and lv[-1] == (0, True))
        for p in (0, 1):
            N = 10 ** 9 + p
            m = stepN(lv, N)
            if m is None: skipped += 1; continue
            r = Z.step_map(tow(word(lv)), N)
            ok = len(r) == 2 and Z.show(r[0]) == word(m[0]) and r[1] == m[1]
            if buried:
                under += 1
            else:
                n += 1
                bad += not ok
    print(f"{n} cases compared, {bad} differ; {skipped} skipped (a count would go negative), "
          f"{under} not compared (a K'(0) next to other items, outside the model)")


if __name__ == '__main__':
    if sys.argv[1] == 'orbit': orbit(int(sys.argv[2]))
    else: rand(int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 1)
