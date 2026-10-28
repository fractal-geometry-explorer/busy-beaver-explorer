"""Which pass starts can the loop's chain from a loop entry of the clean-tape tree reach, and which lanes Q + c = 2^j
do they meet?  (Untrusted; `../lean/END_TO_END.md`, "The chain ends at a right end of at least 769".)

Each entry class is a line z -> (b, W, R) (affine, integer z >= lo, from `../lean/EntryForms.lean`).  The chain from
an entry makes a half pass first or not, then full passes and round-7 breaks; in (b, W, R), with E the start's width,

    half:   b' = (b + E - R + 10)/2,          R' = R/2,                    W' = E + 6   (E = 2 mod 4)
    full:   b' = (b + 48E - 8R + 1250)/64,    R' = R/16,                   W' = E + 24
    break:  b' = (3b + 16E - 6R + 446)/32,    R' = (4E + 4R - b + 110)/32, W' = E + 24

(the walls of `StepMap`, `../lean/BB6/Ends.lean`, through L1 = 147b - 112W + 392R - 186).  The tree here takes every
step on the subclass of the line where its divisions are exact, and imposes nothing else, so it holds every chain the
model makes and more.  A subclass is z = z0 + M u, u >= 0, with the forms in u; it is cut where its least member is
wider than 2^WMAX, so every pass start of a chain with W <= 2^WMAX is a member of a node.  For each node and each
j <= 64 the lane F + c = T (F = Q, 3Q, 2Q - R, Q + R or 2Q + R with Q = W - b + 2R + 22, T = 2^j or 3 * 2^j) holds
at most at one u, and the offsets c with |c| <= CMAX that some member meets are listed, with the census lanes'
offsets (`halting-classes/routes` in the project files, `lanes_r770_1004.txt` for R = 770 to 1,004: Q = 2^j and
3 * 2^j on routes A, C and beta, Q + 36 on C3, C4 and alpha, Q + 636 on delta, epsilon and zeta, 3Q + 76 = 2^j on
A3 and C2, 2Q - R + 6 on A2, and above R = 769 also 2Q - R + 26 = 2^j, Q + 316 = 2^j and Q + 636 = 3 * 2^j, and
Q + 316 = 3 * 2^j at R = 5,350 and 5,862 (`lanes_r5002_5862.txt`); and the lanes of the routes that begin with a half
pass, Q + R + 24, Q + R + 96, Q + R + 1296 and 2Q + R + 60).  Then the same for the lanes the halting-classes sweep
searches with b free at every R of a class (`routes/README.md`, "A census with b free at every R of a class"),
Q + 5 * 2^k - 4 = 2^j or 3 * 2^j for k = 3 to 11 (c = 36 to 10,236, gamma's Q + 5,116 among them), with their forms
before a half pass, Q + R + 24 + 2c; a lane with |c| > CMAX is checked at its own offset.

usage: python3 chain_lanes.py entries36.txt 63 2000   (entries36.txt from `../lean/EntryForms.lean 2199023255552 36`;
       likewise entries40.txt at 40 digits; 74 in place of 63 counts to width 2^74, past the widths at which
       R'^3/L1'^2 leaves the paths on gamma's lane and on Q + 10,236)
"""
import sys
from collections import Counter
from math import gcd

G = 2 ** 41  # the cone: entries of width at least 2^41
# the forms F scanned, as (coefficients of W, b, R, constant); Q = W - b + 2R + 22
FORMS = {'Q': (1, -1, 2, 22), '3Q': (3, -3, 6, 66), '2Q - R': (2, -2, 3, 44), 'Q + R': (1, -1, 3, 22),
         '2Q + R': (2, -2, 5, 44)}
# the census lanes (F, T, c): F + c = T; the last six begin with a half pass, so only an entry can start them
CENSUS = [('Q', '2^j', 0), ('Q', '3*2^j', 0), ('Q', '2^j', 36), ('Q', '3*2^j', 36), ('Q', '2^j', 316),
          ('Q', '3*2^j', 316), ('Q', '2^j', 636), ('Q', '3*2^j', 636), ('3Q', '2^j', 76), ('2Q - R', '2^j', 6),
          ('2Q - R', '3*2^j', 6), ('2Q - R', '2^j', 26), ('Q + R', '2^j', 24), ('Q + R', '3*2^j', 24),
          ('Q + R', '2^j', 96), ('Q + R', '2^j', 1296), ('2Q + R', '2^j', 60), ('2Q + R', '3*2^j', 60)]
# the sweep's lanes Q + c with c = 5 * 2^k - 4, and Q + R + 24 + 2c before a half pass
SWEEP = [(f, t, c) for k in range(3, 12) for f, c in (('Q', 5 * 2 ** k - 4), ('Q + R', 10 * 2 ** k + 16))
         for t in ('2^j', '3*2^j')]


def restrict(forms, f, d, z0, M):
    """The subclass where the form f = A + B u is divisible by d, with the forms in the new coordinate."""
    A, B = f
    g = gcd(B, d)
    if A % g:
        return None
    dd = d // g
    if dd == 1:
        return forms, z0, M
    u1 = ((-A // g) * pow((B // g) % dd, -1, dd)) % dd
    return [(x[0] + x[1] * u1, x[1] * dd) for x in forms], z0 + M * u1, M * dd


def step(kind, st, z0, M):
    b, E, R = st
    if kind == 'H':
        r = restrict([b, E, R], (E[0] - 2, E[1]), 4, z0, M)  # E = 2 (mod 4)
        if r is None:
            return None
        (b, E, R), z0, M = r
        num, dens = [(b[0] + E[0] - R[0] + 10, b[1] + E[1] - R[1]), R, (E[0] + 6, E[1])], [2, 2, 1]
    elif kind == 'F':
        num = [(b[0] + 48 * E[0] - 8 * R[0] + 1250, b[1] + 48 * E[1] - 8 * R[1]), R, (E[0] + 24, E[1])]
        dens = [64, 16, 1]
    else:
        num = [(3 * b[0] + 16 * E[0] - 6 * R[0] + 446, 3 * b[1] + 16 * E[1] - 6 * R[1]),
               (4 * E[0] + 4 * R[0] - b[0] + 110, 4 * E[1] + 4 * R[1] - b[1]), (E[0] + 24, E[1])]
        dens = [32, 32, 1]
    forms = list(num)
    for i in range(3):
        if dens[i] > 1:
            r = restrict(forms, forms[i], dens[i], z0, M)
            if r is None:
                return None
            forms, z0, M = r
            forms[i] = (forms[i][0] // dens[i], forms[i][1] // dens[i])
    return (forms[0], forms[2], forms[1]), z0, M  # (b', W', R')


def main():
    fn, WMAX, CMAX = sys.argv[1], 2 ** int(sys.argv[2]), int(sys.argv[3])
    JMAX = int(sys.argv[2]) + 4  # a form scanned with its offset is below 9W + 2^15 < 2^JMAX (R < W)
    depth, hits = Counter(), {}
    far = {}  # the lanes outside the window, checked one by one: (F, T) -> offsets
    for name, tn, c in CENSUS + SWEEP:
        if abs(c) > CMAX:
            far.setdefault((name, tn), []).append(c)

    def visit(st, umin, cid, shape):
        b, E, R = st
        for name, (cW, cb, cR, c0) in FORMS.items():
            F0, F1 = cW * E[0] + cb * b[0] + cR * R[0] + c0, cW * E[1] + cb * b[1] + cR * R[1]
            assert F1 > 0
            for j in range(30, JMAX):
                for tn, T in (('2^j', 2 ** j), ('3*2^j', 3 * 2 ** j)):
                    # the u with |T - F(u)| <= CMAX
                    for u in range(max(umin, -((F0 + CMAX - T) // F1)), (T - F0 + CMAX) // F1 + 1):
                        if E[0] + E[1] * u > WMAX:
                            break
                        hits.setdefault((name, tn, T - F0 - F1 * u), []).append(
                            (j, cid, shape, E[0] + E[1] * u, R[0] + R[1] * u))
                    for c in far.get((name, tn), ()):
                        u, r = divmod(T - c - F0, F1)
                        if r == 0 and u >= umin and E[0] + E[1] * u <= WMAX:
                            hits.setdefault((name, tn, c), []).append(
                                (j, cid, shape, E[0] + E[1] * u, R[0] + R[1] * u))

    def dfs(st, z0, M, lo, cid, shape):
        b, E, R = st
        umin = max(0, -((z0 - lo) // M))  # least u with z = z0 + M u >= lo
        if E[0] + E[1] * umin > WMAX:
            return
        depth[len(shape)] += 1
        visit(st, umin, cid, shape)
        for k in 'FB':
            r = step(k, st, z0, M)
            if r is not None:
                dfs(r[0], r[1], r[2], lo, cid, shape + k)

    cid = 0
    for line in open(fn):
        if not line.startswith('E '):
            continue
        parts = line[2:].split('|')
        a, b, c, W = [tuple(map(int, p.split()))[:2] for p in parts[1:5]]
        ts = [tuple(map(int, t.split()))[:2] for t in parts[5].split(';')]
        lo = max(-((t[0] - G) // t[1]) for t in ts)
        st = (b, W, (W[0] - c[0] - 1, W[1] - c[1]))
        cid += 1
        dfs(st, 0, 1, lo, cid, '')
        r = step('H', st, 0, 1)
        if r is not None:
            dfs(r[0], r[1], r[2], lo, cid, 'H')
    print('entry classes', cid, 'chain classes with a member of width <= 2^%s:' % sys.argv[2],
          sum(depth.values()), 'by number of steps', sorted(depth.items()))
    for key in sorted(set(k[:2] for k in hits)):
        cs = sorted((k[2] for k in hits if k[:2] == key and abs(k[2]) <= CMAX), key=abs)
        print('lane %s + c = %s: %d offsets with |c| <= %d met, the least' % (key[0], key[1], len(cs), CMAX), cs[:10])
    for key in CENSUS:
        print('census lane %s + %d = %s:' % (key[0], key[2], key[1]), 'met at', hits.get(key, 'none'))
    for key in SWEEP:
        if key not in CENSUS:
            print('sweep lane %s + %d = %s:' % (key[0], key[2], key[1]), 'met at', hits.get(key, 'none'))


if __name__ == '__main__':
    main()
