"""For each repeating round pattern found by the census, read off its affine map by finite differences (mark model,
tracecycle.round_events) and find where it drives the marks over the reals: the fixed point of the positions as fractions
of the width, and whether the last mark goes to the end (progress) or to a fixed fraction short of it (plateau)."""
import sys, re
sys.path.insert(0, '../rec')
from tracecycle import round_events
from fractions import Fraction as F
import numpy as np
def run(W, marks, P):
    sh = []
    for _ in range(P):
        W, marks, ev = round_events(W, [m[:] for m in marks]); sh.append(''.join(t for t, p in marks))
    return W, marks, sh
seen = {}
INST = {}
REPS = {}
for fn in ['pat_rec.txt', 'pat_deep.txt', 'pat_plane.txt', 'pat_plane52.txt', 'pat_mline.txt']:
    for l in open(fn):
        m = re.match(r'\s+(\d+) times, up to (\d+) periods: (\S+)', l)
        if m: REPS[m.group(3)] = max(REPS.get(m.group(3), 0), int(m.group(2)))
for fn in sys.argv[1:]:
    for l in open(fn):
        if not l.startswith('PATNEW'): continue
        m = re.match(r'PATNEW (\d+) (\S+) \| start\((\w+)\) (.*?) width=(\d+) \| seq (.*)', l.strip())
        P = int(m.group(1)); key = m.group(2); toks = m.group(4).split(); W = int(m.group(5)); seq = m.group(6).split()
        if key in seen: continue
        marks = [[t[0], int(t[1:])] for t in toks]
        W1, m1, sh = run(W, marks, P)
        if sh != seq or [t for t, _ in m1] != [t for t, _ in marks]: seen[key] = ('replay differs', P); continue
        n = len(marks); coords = [p for _, p in marks] + [W]; out0 = [p for _, p in m1] + [W1]
        J = None
        for k in (60, 48, 40, 32, 26, 20, 16, 12, 10, 8):
            D = 1 << k; ok = True; cols = []
            if D * 8 > min(coords[1:]) and k > 8: continue
            for j in range(1, n + 1):           # skip the gap at cell 1 (fixed by the rules)
                c = coords[:]; c[j] += D
                mk = [[marks[i][0], c[i]] for i in range(n)]
                W2, m2, sh2 = run(c[n], mk, P)
                if sh2 != seq or [t for t, _ in m2] != [t for t, _ in marks]: ok = False; break
                o = [p for _, p in m2] + [W2]; cols.append([F(o[i] - out0[i], D) for i in range(n + 1)])
            if ok: J = cols; break
        if J is None: seen[key] = ('no clean perturbation', P); continue
        # p_i' = sum_j J[j][i] p_j + const ; columns j = marks 1..n-1, then W
        idx = list(range(1, n))
        M = np.array([[float(J[j - 1][i]) for j in idx] for i in idx]) if idx else np.zeros((0, 0))
        u = np.array([float(J[n - 1][i]) for i in idx])       # coefficient of W
        dW = out0[n] - coords[n]
        ev = np.linalg.eigvals(M) if len(idx) else []
        try: fstar = np.linalg.solve(np.eye(len(idx)) - M, u)
        except Exception: fstar = None
        # the end marker itself always sits at the end; what matters is the last mark before it
        endm = marks[-1][0] == 'M' and marks[-1][1] == W - 2
        inner = list(range(len(idx) - (1 if endm else 0)))
        last = (1 - max(fstar[i] for i in inner)) if (fstar is not None and inner) else None
        seen[key] = (P, n, dW, sorted([complex(e) for e in ev], key=lambda z: -abs(z)), fstar, last, fn, endm)
        INST[key] = (W, marks, [float(x) for x in fstar] if fstar is not None else None)
for key, v in seen.items():
    if isinstance(v[0], str): print('?', v[1], key, v[0]); continue
    P, n, dW, ev, fstar, last, fn, endm = v
    evs = ' '.join(('%.4g' % e.real) if abs(e.imag) < 1e-12 else ('%.3g%+.3gi' % (e.real, e.imag)) for e in ev)
    kind = 'PROGRESS' if last is not None and abs(last) < 1e-9 else 'plateau %.5f W (%.2f halvings)' % (last, -np.log2(last)) if last and last > 0 else 'last mark ' + str(last)
    print('%2d marks %d dW %d reps %d | %s | eig %s | %s%s' % (P, n, dW, REPS.get(key, 0), kind, evs, key, ' (ends with the end marker)' if endm else ''))

import json
json.dump({k: [str(v[0]), [[t, str(p)] for t, p in v[1]], v[2]] for k, v in INST.items()}, open('patinst.json', 'w'))
