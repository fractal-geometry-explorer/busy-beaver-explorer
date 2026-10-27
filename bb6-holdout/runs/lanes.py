"""Past each loop entry of the clean-tape tree, where can the chain's last pass start lie on the main halting lane?
(Untrusted; `../notes/LAB_NOTES.md`, October 27, night, "The chain's last pass start is wide".)

On the main route of the halts found, the run meets the end off the chain at x = (D + 2R + 14)/4, D = W - b, and halves
to 0 when x = 2^j - 2 (or 3 * 2^j - 2), i.e. Q = W - b + 2R + 22 = c * 2^n with c in {1, 3}.

Each entry class is a line z -> (b, W, R) (affine, integer z >= lo, from `../lean/EntryForms.lean`).  Each chain shape
(an optional half pass H, then a word in full passes F and round-7 breaks B) maps it to another line, on the subclass
where the steps' divisions are exact (the steps' inequalities and walls are not imposed, so this is a superset of the
chains).  On a line Q(u) = q0 + q1 u, Q = c 2^n has a solution exactly when c 2^n = q0 (mod q1).  This writes one line
per (class, shape, c), "id c q0modq1 q1 nlo" with nlo the least n with c 2^n at least Q at the cone's edge, for
`lanehit.c`, and the class, shape and forms to out.meta.

usage: python3 lanes.py entries36.txt 3 lines36.txt; cc -O2 -o lanehit lanehit.c; ./lanehit 4096 < lines36.txt
"""
import sys
from math import gcd

G = 2 ** 41  # the cone: entries of width at least 2^41


def parse(fn):
    out = []
    for line in open(fn):
        if not line.startswith('E '):
            continue
        parts = line[2:].split('|')
        D = int(parts[0])
        a, b, c, W = [tuple(map(int, p.split()))[:2] for p in parts[1:5]]
        ts = [tuple(map(int, t.split()))[:2] for t in parts[5].split(';')]
        lo = max(-((t[0] - G) // t[1]) for t in ts)
        out.append((D, b, c, W, lo))
    return out


# a subclass z = z0 + M u of an entry class (z >= lo); forms (k0, k1) mean k0 + k1 u, with integer coefficients
class Cls:
    def __init__(self, lo):
        self.z0, self.M, self.lo = 0, 1, lo


def step(kind, st, cls):
    """st = (b, E, R) as integer forms in the class's u; returns the landing (b', W', R') or None"""
    b, E, R = st
    if kind == 'H':
        num = [(b[0] + E[0] - R[0] + 10, b[1] + E[1] - R[1]), R, (E[0] + 6, E[1])]
        dens = [2, 2, 1]  # b' = (b + E - R + 10)/2, R' = R/2, W' = E + 6, from E = 2 (mod 4)
    elif kind == 'F':
        num = [(b[0] + 48 * E[0] - 8 * R[0] + 1250, b[1] + 48 * E[1] - 8 * R[1]), R, (E[0] + 24, E[1])]
        dens = [64, 16, 1]
    else:  # 'B'
        num = [(3 * b[0] + 16 * E[0] - 6 * R[0] + 446, 3 * b[1] + 16 * E[1] - 6 * R[1]),
               (4 * E[0] + 4 * R[0] - b[0] + 110, 4 * E[1] + 4 * R[1] - b[1]), (E[0] + 24, E[1])]
        dens = [32, 32, 1]
    forms = list(num)
    if kind == 'H':
        res = restrict(forms, (E[0] - 2, E[1]), 4, cls)
        if res is None:
            return None
        forms, cls = res
    for i in range(3):
        if dens[i] == 1:
            continue
        res = restrict(forms, forms[i], dens[i], cls)
        if res is None:
            return None
        forms, cls = res
        forms[i] = (forms[i][0] // dens[i], forms[i][1] // dens[i])
    return (forms[0], forms[2], forms[1]), cls


def restrict(forms, f, d, cls):
    """restrict the class so that d divides f; forms re-expressed"""
    A, B = f
    g = gcd(B, d)
    if A % g:
        return None
    dd = d // g
    if dd == 1:
        return forms, cls
    inv = pow((B // g) % dd, -1, dd)
    u1 = ((-A // g) * inv) % dd
    new = Cls(cls.lo)
    new.z0 = cls.z0 + cls.M * u1
    new.M = cls.M * dd
    forms = [(x[0] + x[1] * u1, x[1] * dd) for x in forms]
    return forms, new


def words(maxlen):
    out = ['']
    for L in range(1, maxlen + 1):
        out += [w + k for w in out if len(w) == L - 1 for k in 'FB']
    return out


def main():
    es = parse(sys.argv[1])
    maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    out = open(sys.argv[3], 'w')
    meta = open(sys.argv[3] + '.meta', 'w')
    shapes = [h + w for h in ('', 'H') for w in words(maxlen)]
    stats = {}
    lid = 0
    big = 0
    for idx, (D, b, c, W, lo) in enumerate(es):
        R = (W[0] - c[0] - 1, W[1] - c[1])
        for sh in shapes:
            cls = Cls(lo)
            st = (b, W, R)
            ok = True
            for k in sh:
                r = step(k, st, cls)
                if r is None:
                    ok = False
                    break
                st, cls = r
            key = sh or '-'
            stats.setdefault(key, 0)
            if not ok:
                continue
            stats[key] += 1
            bP, WP, RP = st
            Q = (WP[0] - bP[0] + 2 * RP[0] + 22, WP[1] - bP[1] + 2 * RP[1])
            ulo = -((cls.z0 - lo) // cls.M)
            q0, q1 = Q
            assert q1 > 0
            if q1 >= 2 ** 62:
                big += 1
                continue
            for cc in (1, 3):
                # smallest n with cc 2^n >= q0 + q1 ulo
                need = q0 + q1 * ulo
                n = 0
                while cc * 2 ** n < need:
                    n += 1
                out.write('%d %d %d %d %d\n' % (lid, cc, q0 % q1, q1, n))
                meta.write('%d %d %s %d %d %d %d %d %d\n' % (lid, idx, key, cc, q0, q1, cls.z0, cls.M, lo))
                lid += 1
    print('lines', lid, 'skipped (q1 >= 2^62)', big, file=sys.stderr)
    for k, v in stats.items():
        print('shape', k, 'entry classes with the shape', v, file=sys.stderr)


main()
