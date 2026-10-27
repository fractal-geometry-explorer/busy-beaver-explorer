"""The main halting route's re-entry into the loop, and why a wide pass start cannot use it (untrusted;
`../notes/LAB_NOTES.md`, October 27, night, "Re-entries").

On the main route (R = 2 mod 8), a pass start with walls a, b, W - R - 1 and width W with D = W - b = 2^(j+2) - 2R - 22
and b in its halting class modulo 2^k meets the end off the chain at x = 2^j - 2, and the run enters the loop again: a
three-wall round start at round 9 with R' = Q/32 (Q = D + 2R + 22), a half pass to round 11 with R' = Q/64, then full
passes down to a halting class.

  runs   CLASSES LEANDIR DYNLIB [scales]   run the mark model (`RunWalls.lean`) from each halting class of a table with
         rows "j R D b0 k rounds" (first wall 449, b = b0 + 2^k t for t = 0, 2) and print its three-wall round starts
         (round, R', L1' = 147 b' + 280 W' - 392 c' - 578);
  fit    CLASSES LEANDIR DYNLIB [scales]   fit L1' at round 11 exactly as an affine form in (b, W, R) on the R = 2
         (mod 8) classes, and check it on every run;
  sigma  bound R'^3 / L1'^2 at round 11 below over every pass start of the lane with the wide shape
         (W <= 64R + 6 or 15W <= 64(W - b), `../lean/thm/WideHalt.lean`) and width at least 2^41, for each scale j.

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


def sigma_bound(j, G=2 ** 41):
    """least R'^3/L1'^2 at round 11 over the lane's wide pass starts of width >= G (None: there are none).  In (R, W)
    the pass starts lie between W = max(D + 898, G) and W = max(64R + 6, 64D/15), D = 2^(j+2) - 2R - 22, two convex
    polygons; |L1'| is convex, so its largest value is at a corner, where two of these lines or R = 178 or the largest R
    (third gap D - R - 1 >= 448) meet."""
    P = 2 ** (j + 2)
    Rmax = (P - 471) // 3
    lines = [(Fr(64), Fr(6)), (Fr(-128, 15), Fr(64 * (P - 22), 15)), (Fr(-2), Fr(P + 876)), (Fr(0), Fr(G))]
    Rs = {178, Rmax}
    for i in range(4):
        for m in range(i + 1, 4):
            (a1, c1), (a2, c2) = lines[i], lines[m]
            if a1 != a2:
                r = (c2 - c1) / (a1 - a2)
                Rs |= {x for x in range(int(r) - 1, int(r) + 3) if 178 <= x <= Rmax}
    mx, any_ = 0, False
    for R in Rs:
        D = 2 ** (j + 2) - 2 * R - 22
        lo, hi = max(D + 898, G), max(64 * R + 6, 64 * D // 15)
        if lo > hi:
            continue
        any_ = True
        for W in (lo, hi):  # L1' is affine, so its extremes are at the corners
            mx = max(mx, abs(L11[0] * (W - D) + L11[1] * W + L11[2] * R + L11[3]))
    return Fr(2 ** (3 * (j - 4))) / mx ** 2 if any_ else None


def main():
    mode = sys.argv[1]
    if mode == 'sigma':
        for j in range(30, 64):
            s = sigma_bound(j)
            print(j, 'no wide pass start of width >= 2^41' if s is None else
                  'min R^3/L^2 = %.4g (%s 177^3/9)' % (s, '>' if s > Fr(177 ** 3, 9) else '<='))
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
