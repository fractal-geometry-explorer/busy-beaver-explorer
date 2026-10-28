"""Which lane values can a route's last pass start close from, by the close's own L1?  (Untrusted;
`../lean/END_TO_END.md`, "The small ends".)

`lane_sigma.py` keeps a lane value against a close when R'^3/L1'^2, at its least over the lane value's pass starts, is
at most r^3/l^2 for an r of the closing set with R' = 16^p r, l the least |L1| of r's class.  But from the last pass
start (W' = 0 mod 4, width at least 2^24) a chain that ends in a closing class is p full passes
(`LoopChain.close_wide` in `../lean/thm/LoopTheorem.lean`), which divide R by exactly 16 and L1 by exactly 64, so the
close has R = r = R'/16^p and L1 = l = L1'/64^p itself, with l in r's class (`closeClasses`: l = c mod m) and
l = 3 (mod 7) (`loopL1_mod7`), as `EntryNoClose.no_close` asks of a loop entry (`../lean/thm/RouteEntryHalt.lean`).
L1' is affine on the lane value's polygon of pass starts, so it lies between its values at the corners, [Lmin, Lmax]
(`end_l1.l1_range`).  The forms, the polygon and the routes are `lane_sigma.py`'s, read with its functions; the forms
of a path seen at one R are taken at every R, as there.  Prints, per route, the lane values that r^3/l^2 at a close
leaves and those the close's own L1 leaves, with r, the interval of l and its values in r's class, and the widest pass
start of each.  With --closeC the classes are those of `closeClassC` (`lane_sigma.py`).

usage: python3 close_l1.py [--floor=66] [--closeC] FORMS...   (`lane_sigma.py`'s files, in `halting-classes/routes`)
"""
import sys
from fractions import Fraction as Fr
from math import ceil, floor, log2

import end_l1
import lane_sigma as ls


def in_class(r, lo, hi):
    """the l in [lo, hi] in r's closing class with l = 3 (mod 7): a list of at most 6, else their count"""
    m, c = ls.CLOSE[r]
    first = next(x for x in range(7 * m) if x % m == c and x % 7 == 3)
    first += 7 * m * ceil((lo - first) / (7 * m))
    n = 0 if first > hi else floor((hi - first) / (7 * m)) + 1
    return [first + 7 * m * i for i in range(n)] if n <= 6 else n


def width(Rf, N):
    """log2 of the widest pass start of the lane value N, 64D/15 at R = 769"""
    return log2(64 * Fr(N - Rf[0]['R'] * ls.RLO - Rf[0]['1'], Rf[0]['W']) / 15)


def main():
    args = sys.argv[1:]
    for a in [a for a in args if a.startswith('--floor=')]:
        ls.G = 2 ** int(a[len('--floor='):])
        args.remove(a)
    if '--closeC' in args:
        ls.CLOSE = ls.CLOSE_C
        args.remove('--closeC')
    found = {}
    for fn in args:
        for src, rnd, Rf, Lf in ls.routes(fn):
            Rf, Lf = ls.norm(Rf), ls.norm(Lf)
            key = (tuple(Rf[0].values()), Rf[1], tuple(Lf[0].values()), Lf[1])
            found.setdefault(key, ([], rnd, Rf, Lf))[0].append(src)
    nsig = nleft = 0
    for srcs, rnd, Rf, Lf in found.values():
        form, s = ls.lane(Rf)
        sig, left, wsig, wleft = [], [], None, None
        for c in (1, 3):
            for e in ls.ES:
                N = c * 2 ** e * s
                sg = ls.sigma_min(Rf, Lf, N)
                if sg is None:
                    continue
                Rp = Fr(N, Rf[1])
                if sg > ls.end_bound(Rp):
                    continue
                sig.append('%d * 2^%d' % (c, e))
                wsig = max(wsig or 0, width(Rf, N))
                Lmin, Lmax = end_l1.l1_range(Rf, Lf, N)
                for r in ls.CLOSE:
                    for p in range(64):
                        if Rp != r * 16 ** p:
                            continue
                        lo, hi = Lmin / 64 ** p, Lmax / 64 ** p
                        ls_ = in_class(r, lo, hi)
                        if ls_:
                            left.append('%d * 2^%d, r = %d: l in [%.4g, %.4g], %s' % (
                                c, e, r, float(lo), float(hi), ls_ if isinstance(ls_, list) else '%d values' % ls_))
                            wleft = max(wleft or 0, width(Rf, N))
        nsig += bool(sig)
        nleft += bool(left)
        if sig:
            print('%s = 2^j or 3 * 2^j at round %d, from %s:' % (form, rnd, ls.where(srcs)))
            print('   r^3/l^2 at a close leaves %s (widths up to 2^%.1f)' % (', '.join(sig), wsig))
            print('   the close\'s own L1 leaves %s' % (
                '; '.join(left) + ' (widths up to 2^%.1f)' % wleft if left else 'none'))
    print('routes with a lane value left against a close: by r^3/l^2 %d, by the close\'s own L1 %d (of %d)' % (
        nsig, nleft, len(found)))


if __name__ == '__main__':
    main()
