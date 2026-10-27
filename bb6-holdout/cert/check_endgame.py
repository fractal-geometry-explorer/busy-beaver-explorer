"""Independent checker for the endgame certificate (October 24).

The certificate (endgame_leaves.txt) lists, for every even R from 2 to 4096, residue classes ("leaves") of the start
state G 1, W a, W b, W c = E - R - 1 (width E) together with the claimed outcome of the mark rules on that class.  This
program re-derives each outcome with its own small implementation of the rules on symbolic positions, with every
digit test decided by the class and every order comparison decided on the cone of large gaps, and verifies that the
leaves of each R partition the valid start class.  It then reports the closing R values, the L1 class of every
closing leaf, the pass condition, and the bound 3 log2 R - 2 log2 |L1|min.

usage: python3 check_endgame.py endgame_leaves.txt
"""
import sys, re, math
from fractions import Fraction as F

# ---------- affine forms in (a, b, E): tuples (ca, cb, cE, c0) of Fractions ----------
def form(ca=0, cb=0, cE=0, c0=0): return (F(ca), F(cb), F(cE), F(c0))
def add(p, q): return tuple(x + y for x, y in zip(p, q))
def sub(p, q): return tuple(x - y for x, y in zip(p, q))
def addc(p, k): return (p[0], p[1], p[2], p[3] + k)
def half(p): return tuple(x / 2 for x in p)
def isconst(p): return p[0] == 0 and p[1] == 0 and p[2] == 0

def sign(p, R):
    """sign of a form on the cone of large gaps t1 = a, t2 = b - a, t3 = c - b (c = E - R - 1); None if undecided"""
    ca, cb, cE, c0 = p
    g1, g2, g3 = ca + cb + cE, cb + cE, cE
    const = cE * (R + 1) + c0
    gs = [g1, g2, g3]
    if all(g == 0 for g in gs): return (const > 0) - (const < 0)
    if all(g >= 0 for g in gs): note_margin(gs, const); return 1
    if all(g <= 0 for g in gs): note_margin(gs, const); return -1
    return None

GAMMA = [F(0)]
import os
NOPHASE = os.environ.get('CHECK_NOPHASE') == '1'   # the start is any G W W W tape, not only a phase-0 pass start
GAMMA_BY = {}
def note_margin(gs, c):
    # the decision is exact when the gap part exceeds the opposing constant: sum g_i t_i > |c| holds for all gaps t_i >= G
    # as soon as G > |c| / sum |g_i|; record the largest such threshold over every decided comparison
    if (c < 0 and any(g > 0 for g in gs)) or (c > 0 and any(g < 0 for g in gs)):
        thr = abs(c) / sum(abs(g) for g in gs)
        if thr > GAMMA[0]: GAMMA[0] = thr
        key = tuple(i + 1 for i, g in enumerate(gs) if g)
        if thr > GAMMA_BY.get(key, F(0)): GAMMA_BY[key] = thr
class Undecided(Exception): pass
class Uncovered(Exception): pass

class Coset:
    """x = x0 + B y, B lower triangular, over (a, b, E)"""
    def __init__(self, x0, B): self.x0 = x0; self.B = B
    def residue(self, p, m):
        """p mod m on the coset, if decided; else raise Undecided"""
        f0 = p[3] + sum(p[i] * self.x0[i] for i in range(3))
        g = [sum(p[i] * self.B[i][k] for i in range(3)) for k in range(3)]
        if f0.denominator != 1 or any(x.denominator != 1 for x in g): raise Undecided('non-integral')
        if any(int(x) % m for x in g): raise Undecided('mod %d' % m)
        return int(f0) % m

LEN = {'G': 3, 'M': 2, 'W': 2, 'B': 3}; VAL = {'G': 0, 'M': 1, 'W': 0, 'B': 1}

def run_round(marks, W, cos, R, chain):
    """one round of the mark rules; marks: list of [type, form]; returns (marks, W, end meetings as (d, kind)) and
    raises Uncovered for configurations the proven rules do not cover.  chain: dict with lastD, lastKind."""
    marks = [[t, p] for t, p in marks]
    def srt(): marks.sort(key=lambda m: _key(m[1]))
    def _key(p):   # order on the cone: compare with every other mark pairwise instead (sorting needs a total order)
        return p
    def less(p, q):
        s = sign(sub(p, q), R)
        if s is None: raise Undecided('order')
        return s < 0
    def sort_marks():
        # insertion sort with cone comparisons
        for i in range(1, len(marks)):
            j = i
            while j > 0 and less(marks[j][1], marks[j - 1][1]): marks[j], marks[j - 1] = marks[j - 1], marks[j]; j -= 1
    def end_of(m): return addc(m[1], LEN[m[0]] - 1)
    def first_right(x):
        best = None
        for m in marks:
            if less(x, m[1]) and (best is None or less(m[1], best[1])): best = m
        return best
    def last_mark():
        best = None
        for m in marks:
            if best is None or less(best[1], m[1]): best = m
        return best
    def left_neighbour(m):
        best = None
        for k in marks:
            if k is not m and less(k[1], m[1]) and (best is None or less(best[1], k[1])): best = k
        return best
    def touches_left(m):
        k = left_neighbour(m)
        return k if (k is not None and isconst(sub(addc(end_of(k), 1), m[1])) and sub(addc(end_of(k), 1), m[1])[3] == 0) else None
    meets = []
    def packet_back(x):
        nonlocal W
        b = None
        for m in marks:
            if m[0] != 'M' and less(m[1], x) and (b is None or less(b[1], m[1])): b = m
        for m in marks:
            if m[0] == 'M' and less(m[1], x) and (b is None or less(b[1], m[1])):
                k = touches_left(m)
                if k is not None and k[0] in 'WG': raise Uncovered('packet meets marker after ' + k[0])
        if b is None: return None
        if b[0] == 'B': raise Uncovered('packet reaches a block (halt)')
        if b[0] == 'G': b[1] = addc(b[1], 2); return b
        k = touches_left(b)
        if k is not None and VAL[k[0]] == 0: raise Uncovered('packet meets wall after a 0-mark')
        q = b[1]; b[0] = 'M'; b[1] = addc(q, -1); g = ['G', addc(q, 1)]; marks.append(g); return g
    def shift_from(x):
        nonlocal W
        k = first_right(x)
        if k is None:
            W = addc(W, 2); e = ['M', addc(W, -2)]; marks.append(e); return packet_back(addc(W, -2))
        if k[0] == 'M': k[0] = 'G'; return k
        if k[0] == 'W': k[0] = 'B'; return packet_back(k[1])
        if k[0] == 'B':
            # a block that ends the tape (nothing after it, W = k + 3): the wall it leaves would take the cells W - 1
            # and W, which is blank tape, so write that tape's canonical form, no wall and width W - 1, as the proved
            # model does (roundZ in ../lean/BB6/Round.lean).  Keeping the wall was the "trailing-wall slip".
            if first_right(k[1]) is None:
                dd = sub(W, k[1])
                if isconst(dd):
                    if dd[-1] < 3: raise Uncovered('block past the tape end')
                    if dd[-1] == 3: marks.remove(k); W = addc(W, -1); return packet_back(k[1])
                elif sign(addc(dd, -4), R) != 1: raise Undecided('block at the tape end')
            k[0] = 'W'; k[1] = addc(k[1], 2); return packet_back(k[1])
        raise Uncovered('shift meets a sleeping gap')
    sort_marks()
    gap = marks[0]; guard = 0
    while gap is not None:
        guard += 1
        if guard > 1000: raise Uncovered('round too long')
        g = gap[1]; m = first_right(g)
        kl = touches_left(gap)
        if kl is not None and VAL[kl[0]] == 0: raise Uncovered('gap after a 0-mark')
        if m is None:
            marks.remove(gap); W = addc(W, 3); e = ['M', addc(W, -2)]; marks.append(e); gap = packet_back(addc(W, -2))
        elif m[0] == 'M':
            d = addc(sub(m[1], g), -3)
            if isconst(d):
                if d[3] < 0: raise Uncovered('gap overlaps marker')
            else:
                # a meeting at a non-constant distance must be at d >= 4 for the swap/merge rules to apply and for it
                # not to be a close; decided on the cone, and the margin of this decision is recorded like any other
                s = sign(addc(d, -3), R)
                if s is None: raise Undecided('d sign')
                if s < 0: raise Uncovered('meeting at distance below 4')
            if cos.residue(d, 2) != 0: raise Uncovered('odd distance')
            r4 = cos.residue(d, 4)
            is_end = m is last_mark()
            if is_end:
                kind = 'swap' if r4 == 0 else 'merge'
                meets.append((d, kind))
                if isconst(d) and d[3] <= 2: return marks, W, meets, True      # the close: the round's rest is irrelevant
            if r4 == 0:
                h = half(d); m[1] = addc(add(g, h), -1); gap[1] = addc(add(g, h), 1)
            else:
                marks.remove(gap); m[0] = 'W'; m[1] = addc(add(g, half(d)), 3); gap = packet_back(m[1])
        elif m[0] == 'W':
            x = m[1]; marks.remove(gap); marks.remove(m); gap = shift_from(x)
        elif m[0] == 'B':
            m[0] = 'W'; m[1] = addc(m[1], -1); gap = shift_from(m[1])
        else:
            raise Uncovered('gap meets a sleeping gap')
        sort_marks()
        for i in range(1, len(marks)):
            s = sign(sub(marks[i][1], end_of(marks[i - 1])), R)
            if s is None: raise Undecided('overlap test')
            if s <= 0: raise Uncovered('marks overlap')
    extra = 2
    if marks and marks[0][0] == 'M' and isconst(marks[0][1]) and marks[0][1][3] == 0:
        marks[0][0] = 'W'; marks[0][1] = form(0, 0, 0, 1); extra = 4
    for m in marks: m[1] = addc(m[1], extra)
    W = addc(W, extra); marks.insert(0, ['G', form(0, 0, 0, 1)])
    return marks, W, meets, False

def pred(d, kind): return half(addc(d, -2)) if kind == 'merge' else addc(half(d), 4)

def verify_leaf(R, kind, dclaim, cos, rounds, shapes):
    a, b, E = form(1), form(0, 1), form(0, 0, 1)
    c = addc(E, -(R + 1))
    marks = [['G', form(0, 0, 0, 1)], ['W', a], ['W', b], ['W', c]]; W = E
    lastD = None; lastKind = None; hist = []
    for rd in range(1, rounds + 1):
        marks, W, meets, closed = run_round(marks, W, cos, R, None)
        sh = ''.join(m[0] for m in marks)
        hist.append(sh)
        if not closed and sh != shapes[rd - 1]: return 'shape mismatch at round %d: %s vs %s' % (rd, sh, shapes[rd - 1])
        for d, k in meets:
            if lastD is not None and not isconst(d):
                pr = pred(lastD, lastKind)
                if sub(pr, d) != (0, 0, 0, 0):
                    return 'ok' if (kind == 'break' and rd == rounds) else 'unexpected break at round %d' % rd
            lastD, lastKind = d, k
            if isconst(d) and d[3] <= 2:
                return ('ok' if (kind == 'close' and rd == rounds and int(d[3]) == dclaim) else 'unexpected close at round %d (d = %s)' % (rd, d[3]))
        if not NOPHASE:
            if rd == 1 and sh != 'GBW': return 'ok' if kind == 'notphase0' and rounds == 1 else 'phase break at round 1'
            if rd == 2 and sh != 'GMB': return 'ok' if kind == 'notphase0' and rounds == 2 else 'phase break at round 2'
        if rd >= 3 and hist[-3:] == ['GWWW', 'GBW', 'GMB'] and rd - 3 >= 1:
            return 'ok' if (kind == 'pass' and rd == rounds) else 'unexpected pass at round %d' % rd
    return 'no outcome reached (claimed %s)' % kind

# ---------- lattice helpers for the partition check ----------
def hnf_cols(cols):
    """Hermite normal form (lower triangular, columns generate the same lattice) of a list of integer 3-vectors"""
    M = [list(c) for c in cols]
    basis = []
    rows = 3
    for r in range(rows):
        # bring gcd of row r entries (over remaining columns) into one column
        col = [c for c in M if any(c[i] != 0 for i in range(r, rows))]
        M = col
        while True:
            nz = [c for c in M if c[r] != 0]
            if len(nz) <= 1: break
            nz.sort(key=lambda c: abs(c[r]))
            piv = nz[0]
            for c in nz[1:]:
                q = c[r] // piv[r]
                for i in range(rows): c[i] -= q * piv[i]
        nz = [c for c in M if c[r] != 0]
        if nz:
            piv = nz[0]
            if piv[r] < 0: piv[:] = [-x for x in piv]
            basis.append(piv); M = [c for c in M if c is not piv]
        else:
            basis.append(None)
    return basis   # basis[r] has leading nonzero at row r (or None)

def in_lattice(v, basis):
    v = list(v)
    for r in range(3):
        if basis[r] is None:
            if v[r] != 0: return False
            continue
        if v[r] % basis[r][r]: return False
        q = v[r] // basis[r][r]
        for i in range(3): v[i] -= q * basis[r][i]
    return all(x == 0 for x in v)

def cosets_intersect(c1, c2):
    cols = [[c1.B[i][k] for i in range(3)] for k in range(3)] + [[c2.B[i][k] for i in range(3)] for k in range(3)]
    basis = hnf_cols(cols)
    diff = [c1.x0[i] - c2.x0[i] for i in range(3)]
    return in_lattice(diff, basis)

def lattice_index(B):
    return abs(B[0][0] * (B[1][1] * B[2][2] - B[1][2] * B[2][1]) - B[0][1] * (B[1][0] * B[2][2] - B[1][2] * B[2][0]) + B[0][2] * (B[1][0] * B[2][1] - B[1][1] * B[2][0]))

# ---------- main ----------
leaves = {}
pat = re.compile(r'L R=(\d+) (\w+) bits=(\d+) d=(-?\d+) x0=(-?\d+),(-?\d+),(-?\d+) B=(-?\d+),(-?\d+),(-?\d+),(-?\d+),(-?\d+),(-?\d+) rounds=(\d+) \| (.*)')
for line in open(sys.argv[1]):
    m = pat.match(line)
    if not m: continue
    R, kind, bits, d = int(m.group(1)), m.group(2), int(m.group(3)), int(m.group(4))
    x0 = [F(int(m.group(i))) for i in (5, 6, 7)]; b = [int(m.group(i)) for i in range(8, 14)]
    B = [[F(b[0]), F(0), F(0)], [F(b[1]), F(b[2]), F(0)], [F(b[3]), F(b[4]), F(b[5])]]
    leaves.setdefault(R, []).append((kind, bits, d, Coset(x0, B), int(m.group(14)), m.group(15).split()))
print('R values:', len(leaves), '; leaves:', sum(len(v) for v in leaves.values()))
bad = 0; closes = {}; passes = []; und = 0; unc = 0
for R in sorted(leaves):
    L = leaves[R]
    # partition: every leaf inside the valid start class (a odd, b even, E even), total measure 1, pairwise disjoint
    tot = F(0)
    for kind, bits, d, cos, rounds, shapes in L:
        if int(cos.x0[0]) % 2 != 1 or int(cos.x0[1]) % 2 or int(cos.x0[2]) % 2: print('R', R, 'leaf outside the start class'); bad += 1
        idx = lattice_index([[int(x) for x in row] for row in cos.B])
        if idx != 8 * 2 ** bits: print('R', R, 'index mismatch', idx, bits); bad += 1
        tot += F(1, 2 ** bits)
    if tot != 1: print('R', R, 'leaves cover measure', tot, 'not 1'); bad += 1
    for i in range(len(L)):
        for j in range(i + 1, len(L)):
            if cosets_intersect(L[i][3], L[j][3]): print('R', R, 'leaves', i, j, 'intersect'); bad += 1
    # outcomes
    for kind, bits, d, cos, rounds, shapes in L:
        try:
            res = verify_leaf(R, kind, d, cos, rounds, shapes)
        except Undecided as e: res = 'undecided: %s' % e; und += 1
        except Uncovered as e: res = 'uncovered: %s' % e; unc += 1
        if res != 'ok': print('R', R, kind, 'rounds', rounds, '->', res); bad += 1
        if kind == 'close':
            # L1 = 147 b + 280 E - 392 c - 578 with c = E - R - 1  ->  147 b - 112 E + 392 R - 186
            Lf = form(0, 147, -112, 392 * R - 186)
            f0 = Lf[3] + sum(Lf[i] * cos.x0[i] for i in range(3)); g = [sum(Lf[i] * cos.B[i][k] for i in range(3)) for k in range(3)]
            mod = 0
            for t in g: mod = math.gcd(mod, int(t))
            closes.setdefault(R, set()).add((int(f0) % mod, mod, d))
        if kind == 'pass':
            Lf = form(0, 147, -112, 392 * R - 186)
            f0 = Lf[3] + sum(Lf[i] * cos.x0[i] for i in range(3)); g = [sum(Lf[i] * cos.B[i][k] for i in range(3)) for k in range(3)]
            mod = 0
            for t in g: mod = math.gcd(mod, int(t))
            passes.append((R, int(f0) % mod, mod))
print('leaf failures:', bad, '; undecided:', und, '; uncovered:', unc)
print('closing R:', sorted(closes))
worst = -99
for R in sorted(closes):
    cl = closes[R]
    # the union of the L1 classes of the closing leaves, reduced to a common modulus
    M = 1
    for r0, mod, d in cl: M = math.lcm(M, mod)
    resid = set()
    for r0, mod, d in cl:
        for k in range(M // mod): resid.add(r0 + k * mod)
    mn = min(abs(x) for x in range(-M, M + 1) if x % M in resid and x % 7 == 3 and x != 0)
    val = 3 * math.log2(R) - 2 * math.log2(mn)
    worst = max(worst, val)
    print(f'  R {R}: L1 in {sorted(resid)} mod {M}; smallest |L1| {mn}; 3 log2 R - 2 log2 |L1| = {val:.2f}; closing d: {sorted(set(d for _, _, d in cl))}')
print(f'bound: log2 W <= sigma + {worst:.2f}')
print('passes from R:', sorted(set(R for R, _, _ in passes)), '; all R = 0 mod 64:', all(R % 64 == 0 for R, _, _ in passes))
print('pass L1 classes:', sorted(set((r0, mod) for _, r0, mod in passes)))
print('every cone decision is exact once every gap exceeds', float(GAMMA[0]), 'cells')
for key in sorted(GAMMA_BY): print('   decisions involving gaps', key, 'are exact once those gaps exceed', float(GAMMA_BY[key]), 'cells')
print('CERTIFICATE', 'VALID' if bad == 0 and und == 0 and unc == 0 else 'INVALID')
