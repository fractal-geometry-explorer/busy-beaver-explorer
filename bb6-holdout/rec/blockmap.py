"""Exact block-to-block maps. A 'block state' is a round start  G1, B r, W R  (nothing else), width w.
Collect transitions to the next block state, group them by the shapes of the rounds in between, and solve for
an exact affine formula  x' = a r + b R + c w + d  (x' = r', R', w') in each group, then verify it on all members."""
import random, collections, itertools
from fractions import Fraction as F
import tracecycle as T
T.HOOK = None
def v2(x):
    c = 0
    while x and x % 2 == 0: x //= 2; c += 1
    return c
def shape(ms): return " ".join(m[0] for m in ms)
random.seed(11)
groups = collections.defaultdict(list)
for t in range(60000):
    n = random.randrange(10**9, 10**13)
    w = 2 * n + 6; marks = [["G", 1], ["M", w - 2]]; hist = []
    for _ in range(300):
        ms = sorted(([a, b] for a, b in marks), key=lambda m: m[1]); hist.append((w, ms))
        w, marks, ev = T.round_events(w, marks)
        if len(marks) == 2 and marks[1] == ["M", w - 2]: break
    idx = [i for i, (ww, ms) in enumerate(hist) if shape(ms) == "G B W"]
    for i, j in zip(idx, idx[1:]):
        path = tuple(shape(hist[k][1]) for k in range(i + 1, j))
        if len(path) > 8: continue
        (w0, m0), (w1, m1) = hist[i], hist[j]
        r, R = m0[1][1], m0[2][1]; r1, R1 = m1[1][1], m1[2][1]
        groups[(path, min(v2(r), 12))].append((r, R, w0, r1, R1, w1))
def solve(rows, k):
    # solve x' = a r + b R + c w + d exactly from 4 independent rows, verify on all
    for combo in itertools.combinations(range(len(rows)), 4):
        A = [[F(rows[i][0]), F(rows[i][1]), F(rows[i][2]), F(1)] for i in combo]; y = [F(rows[i][k]) for i in combo]
        # gaussian elimination
        M = [A[i] + [y[i]] for i in range(4)]
        ok = True
        for c in range(4):
            p = next((i for i in range(c, 4) if M[i][c] != 0), None)
            if p is None: ok = False; break
            M[c], M[p] = M[p], M[c]
            M[c] = [x / M[c][c] for x in M[c]]
            for i in range(4):
                if i != c and M[i][c] != 0: M[i] = [a - M[i][c] * b for a, b in zip(M[i], M[c])]
        if not ok: continue
        coef = [M[i][4] for i in range(4)]
        if all(coef[0] * x[0] + coef[1] * x[1] + coef[2] * x[2] + coef[3] == x[k] for x in rows): return coef
        return None
    return None
def fmt(coef):
    names = ["r", "R", "w", ""]; parts = []
    for c, nm in zip(coef, names):
        if c == 0: continue
        parts.append(f"{c}{'·' + nm if nm else ''}")
    return " + ".join(parts).replace("+ -", "− ")
top = sorted(groups.items(), key=lambda kv: -len(kv[1]))[:14]
for (path, z), rows in top:
    if len(rows) < 6: continue
    fs = [solve(rows, k) for k in (3, 4, 5)]
    pth = " → ".join(path) if path else "(next round)"
    print(f"{len(rows):5d}×  r has {z} trailing zeros; rounds between: {pth}")
    for nm, f in zip(("r'", "R'", "w'"), fs): print(f"        {nm} = {fmt(f) if f else 'no single affine formula'}")
