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
j < WMAX + 4 the lane F + c = T (F = Q, 3Q, 2Q - R, Q + R or 2Q + R with Q = W - b + 2R + 22, T = 2^j or 3 * 2^j) holds
at most at one u, and the offsets c with |c| <= CMAX that some member meets are listed, with the census lanes'
offsets (`halting-classes/routes` in the project files, `lanes_r770_1004.txt` for R = 770 to 1,004: Q = 2^j and
3 * 2^j on routes A, C and beta, Q + 36 on C3, C4 and alpha, Q + 636 on delta, epsilon and zeta, 3Q + 76 = 2^j on
A3 and C2, 2Q - R + 6 on A2, and above R = 769 also 2Q - R + 26 = 2^j, Q + 316 = 2^j and Q + 636 = 3 * 2^j, and
Q + 316 = 3 * 2^j at R = 5,350 and 5,862 (`lanes_r5002_5862.txt`); and the lanes of the routes that begin with a half
pass, Q + R + 24, Q + R + 96, Q + R + 1296 and 2Q + R + 60); a lane with |c| > CMAX is checked at its own offset.
Then the family of lanes that the halting-classes sweep searches with b free at every R of a class (`routes/README.md`,
"A census with b free at every R of a class"), Q + 5 * 2^k - 4 = 2^j or 3 * 2^j, there for k = 3 to 11 (c = 36 to
10,236, gamma's Q + 5,116 at k = 10), which goes on for every k = 2 or 3 (mod 4) (the walls make (k - 6)/4 or
(k - 7)/4 passes of a 4-wall loop on the way, the route-completeness side finds), with its forms before a half pass,
Q + R + 24 + 2c = Q + R + 10 * 2^k + 16: at every k from 3 with c below 2^(WMAX + 4), so at every lane of the family
that a member up to width 2^WMAX can meet, each by the residue of T modulo the step of the form.  (A start is on the
family when the odd part m of Q - 4 has m + 5 = 2^i or 3 * 2^i, k being the power of 2 in Q - 4, so a class whose Q has
a small odd step meets it at many k.)  From the entry of each member met on a census lane or the family the run is then
followed in the mark model of `../rec/clean_recurrence.py` (checked there against the machine) to the next clean tape
or a halt.

usage: python3 chain_lanes.py entries36.txt 63 2000   (entries36.txt from `../lean/EntryForms.lean 2199023255552 36`;
       likewise entries40.txt at 40 digits; 74 in place of 63 counts to width 2^74, past the widths at which
       R'^3/L1'^2 leaves the paths on gamma's lane and on Q + 10,236, and 128 or 256 on, for the family's later lanes,
       which it leaves to larger widths)
"""
import os
import sys
from collections import Counter
from math import gcd

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'rec'))
from clean_recurrence import _round, Halt  # the mark model, checked against the machine

G = 2 ** 41  # the cone: entries of width at least 2^41
# the forms F scanned, as (coefficients of W, b, R, constant); Q = W - b + 2R + 22
FORMS = {'Q': (1, -1, 2, 22), '3Q': (3, -3, 6, 66), '2Q - R': (2, -2, 3, 44), 'Q + R': (1, -1, 3, 22),
         '2Q + R': (2, -2, 5, 44)}
# the census lanes (F, T, c): F + c = T; the last six begin with a half pass, so only an entry can start them
CENSUS = [('Q', '2^j', 0), ('Q', '3*2^j', 0), ('Q', '2^j', 36), ('Q', '3*2^j', 36), ('Q', '2^j', 316),
          ('Q', '3*2^j', 316), ('Q', '2^j', 636), ('Q', '3*2^j', 636), ('3Q', '2^j', 76), ('2Q - R', '2^j', 6),
          ('2Q - R', '3*2^j', 6), ('2Q - R', '2^j', 26), ('Q + R', '2^j', 24), ('Q + R', '3*2^j', 24),
          ('Q + R', '2^j', 96), ('Q + R', '2^j', 1296), ('2Q + R', '2^j', 60), ('2Q + R', '3*2^j', 60)]
# the sweep's family of lanes Q + c with c = 5 * 2^k - 4, and Q + R + 24 + 2c before a half pass: F -> c(k)
FAMILY = {'Q': lambda k: 5 * 2 ** k - 4, 'Q + R': lambda k: 10 * 2 ** k + 16}


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
    for name, tn, c in CENSUS:
        if abs(c) > CMAX:
            far.setdefault((name, tn), []).append(c)
    fam = []  # the members on a lane of the family: (k, F, T, j, entry class, shape, W, R, the entry's z)
    classes = {}  # entry class -> its forms (a, b, c, W) in z

    def visit(st, z0, M, umin, cid, shape):
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
                            (j, cid, shape, E[0] + E[1] * u, R[0] + R[1] * u, z0 + M * u))
                    for c in far.get((name, tn), ()):
                        u, r = divmod(T - c - F0, F1)
                        if r == 0 and u >= umin and E[0] + E[1] * u <= WMAX:
                            hits.setdefault((name, tn, c), []).append(
                                (j, cid, shape, E[0] + E[1] * u, R[0] + R[1] * u, z0 + M * u))
            if name in FAMILY:
                # F(u) + c(k) = T needs T = F0 + c(k) (mod F1): one look-up for each T, not a division for each k
                ks = {}
                for k in range(3, JMAX):
                    ks.setdefault((F0 + FAMILY[name](k)) % F1, []).append(k)
                for j in range(30, JMAX):
                    for tn, T in (('2^j', 2 ** j), ('3*2^j', 3 * 2 ** j)):
                        for k in ks.get(T % F1, ()):
                            u = (T - F0 - FAMILY[name](k)) // F1
                            if u >= umin and E[0] + E[1] * u <= WMAX:
                                fam.append((k, name, tn, j, cid, shape, E[0] + E[1] * u, R[0] + R[1] * u,
                                            z0 + M * u))

    def dfs(st, z0, M, lo, cid, shape):
        b, E, R = st
        umin = max(0, -((z0 - lo) // M))  # least u with z = z0 + M u >= lo
        if E[0] + E[1] * umin > WMAX:
            return
        depth[len(shape)] += 1
        visit(st, z0, M, umin, cid, shape)
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
        classes[cid] = (a, b, c, W)
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
        met = hits.get(key, [])
        print('census lane %s + %d = %s:' % (key[0], key[2], key[1]), 'met at', [m[:5] for m in met] or 'none')
        for j, cid, shape, W, R, z in met:
            print('      the run from the entry of class %d at z = %d:' % (cid, z), run_on(classes[cid], z))
    print('the sweep\'s family Q + 5 * 2^k - 4 = 2^j or 3 * 2^j, and Q + R + 10 * 2^k + 16 before a half pass, '
          'for k = 3 to %d: %d members met' % (JMAX - 1, len(fam)))
    for k, name, tn, j, cid, shape, W, R, z in sorted(fam):
        print('   k = %d, %s + %d = %s at j = %d: entry class %d at z = %d, steps %r, W = %d (%d mod 4), R = %d' % (
            k, name, FAMILY[name](k), tn, j, cid, z, shape, W, W % 4, R))
        print('      the run from the entry:', run_on(classes[cid], z))


def run_on(forms, z, cap=10 ** 4):
    """The run from the loop entry at z of a class (its walls a, b and c and width W) in the mark model, to the next
    clean tape."""
    a, b, c, W = [f[0] + f[1] * z for f in forms]
    w, marks = W, [['G', 1], ['W', a], ['W', b], ['W', c]]
    for r in range(1, cap + 1):
        try:
            w, marks = _round(w, marks)
        except Halt:
            return 'it halts in round %d' % r
        if len(marks) == 2 and marks[1] == ['M', w - 2]:
            return 'a clean tape in round %d, n = %d' % (r, (w - 6) // 2)
    return 'no clean tape within %d rounds' % cap


if __name__ == '__main__':
    main()
