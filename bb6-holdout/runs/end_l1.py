"""Which lane values can a route's last pass start reach an end below 178 from, by the end's own L1?  (Untrusted;
`../lean/END_TO_END.md`, "The small ends".)

`lane_sigma.py` keeps a lane value when R'^3/L1'^2, at its least over the lane value's pass starts, is at most r^3/16 at
an even end r = R'/16^p below 178 (r^3/100 where 8 divides r).  But full passes divide R' by exactly 16 and L1' by
exactly 64 (`LoopOut` in `../lean/BB6/Loop.lean`), so the end's L1 is l = L1'/64^p itself, and L1' is affine on the
lane value's polygon of pass starts (the shape `blank_halt_open_big` gives the chain's last pass start, with the width
floor of `--floor`), so it lies between its values at the corners, [Lmin, Lmax].  The end needs an integer l in
[Lmin, Lmax]/64^p with l = 10 (mod 14) (even and 3 mod 7 at a phase-0 start) whose start does not reach a clean tape at
once (`../lean/thm/PassClean.lean`: l = 4 (mod 8) when 4 | r and r >= 8, `pass_clean_l4`; l = 16 (mod 32) when 8 | r and
r >= 16, `pass_clean_l16`).  The forms, the polygon and the routes are `lane_sigma.py`'s, read with its functions; the
forms of a path seen at one R are taken at every R, as there.  Prints, per route, the lane values r^3/16 leaves and
those the end's L1 leaves, with the interval of l and its admissible values.

usage: python3 end_l1.py [--floor=66] [--no-clean] FORMS...   (the files of `lane_sigma.py`, in `halting-classes/routes`)
"""
import sys
from fractions import Fraction as Fr
from math import ceil, floor

import lane_sigma as ls

CLEAN = True


def l1_range(Rf, Lf, N):
    """[Lmin, Lmax] of L1' over the pass starts of the lane value N, as `lane_sigma.sigma_min` takes them (None: none)"""
    (n, dn), (l, dl) = Rf, Lf
    k, rho, n0 = n['W'], n['R'], n['1']
    d0, d1 = Fr(N - n0, k), Fr(-rho, k)
    if d1 >= 1 or (d0 - 449) / (1 - d1) < ls.RLO:
        return None
    Rmax = (d0 - 449) / (1 - d1)
    lines = [(d0 + 898, d1), (Fr(ls.G), Fr(0)), (64 * d0 / 15, 64 * d1 / 15)]
    Rs = {Fr(ls.RLO), Rmax}
    for i in range(len(lines)):
        for j in range(i + 1, len(lines)):
            (a0, a1), (b0, b1) = lines[i], lines[j]
            if a1 != b1 and ls.RLO <= (b0 - a0) / (a1 - b1) <= Rmax:
                Rs.add((b0 - a0) / (a1 - b1))
    vals = []
    for R in Rs:
        D = d0 + d1 * R
        lo, hi = max(D + 898, Fr(ls.G)), 64 * D / 15
        if lo <= hi:
            vals += [(l['b'] * (W - D) + l['W'] * W + l['R'] * R + l['1']) / Fr(dl) for W in (lo, hi)]
    return (min(vals), max(vals)) if vals else None


def clean(r, l):
    """the end's start reaches a clean tape at once (`../lean/thm/PassClean.lean`)"""
    return CLEAN and ((r % 4 == 0 and r >= 8 and l % 8 == 4) or (r % 8 == 0 and r >= 16 and l % 32 == 16))


def admissible(r, lo, hi):
    """the l in [lo, hi] with l = 10 (mod 14) outside the clean classes: a list of at most 6, else their count (l mod
    224 decides both, so a wide interval is counted, not run through)"""
    a, b = ceil(lo), floor(hi)
    n = sum((b - x) // 224 - (a - 1 - x) // 224 for x in range(224) if x % 14 == 10 and not clean(r, x))
    return [x for x in range(a, b + 1) if x % 14 == 10 and not clean(r, x)] if n <= 6 else n


def main():
    global CLEAN
    args = sys.argv[1:]
    for a in [a for a in args if a.startswith('--')]:
        if a.startswith('--floor='):
            ls.G = 2 ** int(a[len('--floor='):])
        elif a == '--no-clean':
            CLEAN = False
        args.remove(a)
    found = {}
    for fn in args:
        for src, rnd, Rf, Lf in ls.routes(fn):
            Rf, Lf = ls.norm(Rf), ls.norm(Lf)
            key = (tuple(Rf[0].values()), Rf[1], tuple(Lf[0].values()), Lf[1])
            found.setdefault(key, ([], rnd, Rf, Lf))[0].append(src)
    nsmall = nleft = 0
    for srcs, rnd, Rf, Lf in found.values():
        form, s = ls.lane(Rf)
        small, left = [], []
        for c in (1, 3):
            for e in ls.ES:
                N = c * 2 ** e * s
                sg = ls.sigma_min(Rf, Lf, N)
                if sg is None:
                    continue
                Lmin, Lmax = l1_range(Rf, Lf, N)
                Rp = Fr(N, Rf[1])
                for p in range(64):
                    r = Rp / 16 ** p
                    if r.denominator != 1 or r % 2 or not 2 <= r < 178:
                        continue
                    r = int(r)
                    if sg <= Fr(r ** 3, 16):
                        small.append('%d * 2^%d (r = %d)' % (c, e, r))
                    lo, hi = Lmin / 64 ** p, Lmax / 64 ** p
                    ls_ = admissible(r, lo, hi)
                    if ls_:
                        left.append('%d * 2^%d, r = %d: l in [%.4g, %.4g], %s' % (
                            c, e, r, float(lo), float(hi), ls_ if isinstance(ls_, list) else '%d values' % ls_))
        nsmall += bool(small)
        nleft += bool(left)
        if small:
            print('%s at round %d, from %s:' % (form, rnd, ls.where(srcs)))
            print('   r^3/16 leaves %s' % ', '.join(small))
            print('   the end\'s L1 leaves %s' % ('; '.join(left) if left else 'none'))
    print('routes with a lane value left: by r^3/16 %d, by the end\'s L1 %d' % (nsmall, nleft))


if __name__ == '__main__':
    main()
