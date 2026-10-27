"""The halting routes' re-entries into the loop, and why a pass start a halt from blank tape needs uses none of them
(untrusted; `../notes/LAB_NOTES.md`, October 27, night, "Re-entries").

On the main route (R = 2 mod 8), a pass start with walls a, b, W - R - 1 and width W with D = W - b = 2^(j+2) - 2R - 22
and b in its halting class modulo 2^k meets the end off the chain at x = 2^j - 2, and the run enters the loop again: a
three-wall round start at round 9 with R' = Q/32 (Q = D + 2R + 22), a half pass to round 11 with R' = Q/64, then full
passes down to a halting class.  The halting-classes census (R = 178 to 198, D <= 8,192: 72 classes) finds eight
routes, each re-entering at a three-wall start P' at round 2, 7 or 11 whose R' and L1' are affine in (b, W, R) on the
route's class (`ROUTES`; route B is the loop's own half pass, a step of the chain).

  runs   CLASSES LEANDIR DYNLIB [scales]   run the mark model (`RunWalls.lean`) from each halting class of a table with
         rows "j R D b0 k rounds" (first wall 449, b = b0 + 2^k t for t = 0, 2) and print its three-wall round starts
         (round, R', L1' = 147 b' + 280 W' - 392 c' - 578);
  fit    CLASSES LEANDIR DYNLIB [scales]   fit L1' at round 11 exactly as an affine form in (b, W, R) on the R = 2
         (mod 8) classes, and check it on every run;
  sigma  bound R'^3 / L1'^2 at P' below, for each route and lane value, over the pass starts of the lane with width at
         least 2^41 and the shape of `../lean/thm/WideHalt.lean` (W <= 64R + 6 or 15W <= 64(W - b)) or of
         `../lean/thm/FarHalt.lean` (15W <= 64(W - b)), against 177^3/9 (`noSmall_sigma`) and against r^3/9 for the
         right ends r of the halting classes that R' = 16^p r allows.

The table of halting classes comes from the halting-classes work (`HaltClasses.lean search pow j ...`); LEANDIR is
`../lean` after `check_end.sh` (LEAN_PATH set to the library and `out`), DYNLIB its `cbuild/so/libBB6all.so`.
"""
import os
import re
import subprocess
import sys
from fractions import Fraction as Fr
from math import log2

LEAN = os.environ.get('LEAN', 'lean')


def walls_run(leandir, dynlib, a, b, W, R, n):
    """three-wall round starts of the model's run: (round, R', L1', W', b'); and the round of a close at 0, if any"""
    out = subprocess.run([LEAN, '--load-dynlib=' + dynlib, '--run', 'RunWalls.lean', str(a), str(b), str(W), str(R),
                          str(n)], capture_output=True, text=True, cwd=leandir).stdout
    res, close0 = [], None
    for line in out.splitlines()[1:]:
        m = re.match(r'\s+after round (\d+): G(\w*) W=(\d+) R=(-?\d+) end meetings \[([^\]]*)\] positions \[([^\]]*)\]',
                     line)
        if not m:
            if 'CLOSE' in line and '[0]' in line and close0 is None:
                close0 = int(line.split('round ')[1].split(':')[0])
            continue
        r, shape, W1, R1, _, pos = m.groups()
        if shape == 'WWW':
            a1, b1, c1 = map(int, pos.split(', '))
            W1 = int(W1)
            res.append((int(r), int(R1), 147 * b1 + 280 * W1 - 392 * c1 - 578, W1, b1))
    return res, close0


def classes(fn, scales):
    for line in open(fn):
        if line[0].isdigit():
            j, R, D, b0, k = map(int, line.split('\t')[:5])
            if scales is None or j in scales:
                yield j, R, D, b0, k


def solve(rows, ys):
    """exact solution of the first full-rank square subsystem"""
    n = len(rows[0])
    piv = []
    for r, y in zip(rows, ys):
        v = [Fr(x) for x in r] + [Fr(y)]
        for i, p in piv:
            if v[i]:
                f = v[i] / p[i]
                v = [x - f * q for x, q in zip(v, p)]
        nz = [i for i in range(n) if v[i]]
        if nz:
            piv.append((nz[0], v))
        if len(piv) == n:
            break
    sol = [Fr(0)] * n
    for i, p in reversed(piv):
        sol[i] = (p[n] - sum(p[m] * sol[m] for m in range(n) if m != i)) / p[i]
    return sol


L11 = (Fr(-49, 128), Fr(91, 256), Fr(637, 256), Fr(2869, 128))  # L1' at round 11 = -49b/128 + 91W/256 + 637R/256 + 2869/128


G41 = 2 ** 41
SIG = Fr(177 ** 3, 9)  # noSmall_sigma: full passes from R, L end below 178 only if R^3/L^2 <= 177^3/9
HALT_R = (2, 4, 6, 8, 16, 32, 48)  # the right ends of the halting classes (`../lean/thm/PassHaltClasses.lean`)

# route: the lane, D = W - b as an affine function of the lane value P and R; R' at P' from P; L1' at P' as
# (al W + be b + ga R + de)/mu.  The lane values are c 2^n with c = 1 or 3 on every route (the census has c = 3 only on
# A, A2, C3 and C4)
ROUTES = {
    'A':  (lambda P, R: P - 2 * R - 22, lambda P: P / 64, (91, -98, 637, 5738, 256)),          # Q = P
    'A2': (lambda P, R: (P - 3 * R - 50) / 2, lambda P: P / 128, (91, -245, 441, 4562, 256)),   # 2Q - R + 6 = P
    'A3': (lambda P, R: (P - 142 - 6 * R) / 3, lambda P: P / 256, (-308, -441, 1176, 13534, 512)),  # 3Q + 76 = P
    'C':  (lambda P, R: P - 2 * R - 22, lambda P: P / 16, (140, -49, 392, 4366, 32)),            # Q = P
    'C2': (lambda P, R: (P - 142 - 6 * R) / 3, lambda P: P / 64, (385, 441, 0, 10834, 32)),       # 3Q + 76 = P
    'C3': (lambda P, R: P - 58 - 2 * R, lambda P: P / 32, (-840, 343, 343, 740, 32)),          # Q + 36 = P
    'C4': (lambda P, R: P - 58 - 2 * R, lambda P: P / 128, (-504, -245, 784, 8438, 512)),      # Q + 36 = P
}


def sigma_min(route, P, far, G=G41):
    """least R'^3/L1'^2 at P' over the pass starts of the lane with width >= G and the shape (None: there are none).
    In (R, W), with D fixed by the lane, the pass starts lie between W = max(D + 898, G) and W = 64D/15 (far) or
    max(64R + 6, 64D/15), for 178 <= R <= the largest R with third gap D - R - 1 >= 448; R' is fixed by the lane and
    |L1'| is convex, so its largest value is at a corner, where two of these lines or the ends of the R range meet."""
    Df, Rp, (al, be, ga, de, mu) = ROUTES[route]
    P = Fr(P)
    d0 = Fr(Df(P, Fr(0)))
    d1 = Fr(Df(P, Fr(1))) - d0
    Rmax = (d0 - 449) / (1 - d1)
    if Rmax < 178:
        return None
    lines = [(d0 + 898, d1), (Fr(G), Fr(0)), (64 * d0 / 15, 64 * d1 / 15)] + ([] if far else [(Fr(6), Fr(64))])
    Rs = {Fr(178), Rmax}
    for i in range(len(lines)):
        for m in range(i + 1, len(lines)):
            (a0, a1), (b0, b1) = lines[i], lines[m]
            if a1 != b1 and 178 <= (b0 - a0) / (a1 - b1) <= Rmax:
                Rs.add((b0 - a0) / (a1 - b1))
    mx = None
    for R in Rs:
        D = d0 + d1 * R
        lo, hi = max(D + 898, G), (64 * D / 15 if far else max(64 * R + 6, 64 * D / 15))
        if lo <= hi:
            for W in (lo, hi):
                L = abs(al * W + be * (W - D) + ga * R + de) / mu
                mx = L if mx is None else max(mx, L)
    return None if mx is None else Rp(P) ** 3 / mx ** 2


def end_bound(Rp):
    """the largest r^3/9 over the right ends r of the halting classes with R' = 16^p r (None: none)"""
    rs = [r for r in HALT_R if any(Rp == r * 16 ** p for p in range(64))]
    return max((Fr(r ** 3, 9) for r in rs), default=None)


def main():
    mode = sys.argv[1]
    if mode == 'sigma':
        for far in (False, True):
            print('shape', '15W <= 64(W - b)' if far else 'W <= 64R + 6 or 15W <= 64(W - b)')
            for route, (_, Rp, _) in ROUTES.items():
                vals = [(sigma_min(route, c * 2 ** n, far), c, n) for c in (1, 3) for n in range(20, 100)]
                vals = [(s, c, n) for s, c, n in vals if s is not None]
                low = [(c, n) for s, c, n in vals if s <= SIG]
                lowH = [(c, n) for s, c, n in vals if end_bound(Rp(Fr(c * 2 ** n))) is not None and
                        s <= end_bound(Rp(Fr(c * 2 ** n)))]
                print('  %-2s lane values %d, least R^3/L^2 %.4g; at or below 177^3/9 at %d, at or below r^3/9 at %d %s'
                      % (route, len(vals), min(s for s, _, _ in vals), len(low), len(lowH), lowH[:4]))
        return
    fn, leandir, dynlib = sys.argv[2:5]
    scales = set(map(int, sys.argv[5].split(','))) if len(sys.argv) > 5 else None
    data = []
    for j, R, D, b0, k in classes(fn, scales):
        if mode == 'fit' and R % 8 != 2:
            continue
        for t in (0, 2):
            b = b0 + 2 ** k * t
            while b < 898:
                b += 2 ** k
            W = b + D
            res, close0 = walls_run(leandir, dynlib, 449, b, W, R, 2 * j + 6)
            if mode == 'runs':
                print(j, R, t, W, 'close at 0 in round', close0, [(r, R1, L1) for r, R1, L1, _, _ in res])
            r11 = [x for x in res if x[0] == 11]
            if r11:
                data.append((b, W, R, r11[0][2], r11[0][1], (D + 2 * R + 22) // 64))
    if mode == 'fit':
        sol = solve([(b, W, R, 1) for b, W, R, _, _, _ in data], [L for _, _, _, L, _, _ in data])
        bad = sum(1 for b, W, R, L, R1, q in data if sol[0] * b + sol[1] * W + sol[2] * R + sol[3] != L or R1 != q)
        print('L1\' at round 11 =', ' + '.join('%s*%s' % (c, v) for c, v in zip(sol, ('b', 'W', 'R', '1'))),
              '; R\' = Q/64; runs', len(data), 'misfits', bad)


if __name__ == '__main__':
    main()
