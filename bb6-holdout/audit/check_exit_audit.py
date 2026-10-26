"""Independent checker for the EXIT certificate (October 24): from a loop state G 1, W a, W b, W c, width E, every
position free, each leaf is either a completed pass of the plain loop (in either phase) or an exit; the checker
verifies the partition, every leaf's rounds, the number of chained end meetings, and that no exit re-enters the loop.
(Derived from check_endgame.py; the forms have four variables and the cone has four gaps.)
"""
if False:  # (the endgame docstring follows, kept for reference)
    """

The certificate (endgame_leaves.txt) lists, for every even R from 2 to 4096, residue classes ("leaves") of the start
state G 1, W a, W b, W c = E - R - 1 (width E) together with the claimed outcome of the mark rules on that class.  This
program re-derives each outcome with its own small implementation of the rules on symbolic positions, with every
digit test decided by the class and every order comparison decided on the cone of large gaps, and verifies that the
leaves of each R partition the valid start class.  It then reports the closing R values, the L1 class of every
closing leaf, the pass condition, and the bound 3 log2 R - 2 log2 |L1|min.

usage: python3 check_endgame.py endgame_leaves.txt
"""
import sys, re, math
import atexit
AUDIT = {}
AUDIT_EX = []
atexit.register(lambda: print('AUDIT shifts reaching the last mark:', sorted(AUDIT.items(), key=str), '\nAUDIT cases at or past the tape end:', len(AUDIT_EX), AUDIT_EX[:10], flush=True))
from fractions import Fraction as F

# ---------- affine forms in (a, b, E): tuples (ca, cb, cE, c0) of Fractions ----------
def form(ca=0, cb=0, cc=0, cE=0, c0=0): return (F(ca), F(cb), F(cc), F(cE), F(c0))
def add(p, q): return tuple(x + y for x, y in zip(p, q))
def sub(p, q): return tuple(x - y for x, y in zip(p, q))
def addc(p, k): return (p[0], p[1], p[2], p[3], p[4] + k)
def half(p): return tuple(x / 2 for x in p)
def isconst(p): return p[0] == 0 and p[1] == 0 and p[2] == 0 and p[3] == 0

def sign(p, R=None):
    """sign of a form on the cone of large gaps t1 = a, t2 = b - a, t3 = c - b, t4 = E - c; None if undecided"""
    ca, cb, cc, cE, c0 = p
    gs = [ca + cb + cc + cE, cb + cc + cE, cc + cE, cE]
    if all(g == 0 for g in gs): return (c0 > 0) - (c0 < 0)
    if all(g >= 0 for g in gs): note_margin(gs, c0); return 1
    if all(g <= 0 for g in gs): note_margin(gs, c0); return -1
    return None

GAMMA = [F(0)]
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
        f0 = p[4] + sum(p[i] * self.x0[i] for i in range(4))
        g = [sum(p[i] * self.B[i][k] for i in range(4)) for k in range(4)]
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
        return k if (k is not None and isconst(sub(addc(end_of(k), 1), m[1])) and sub(addc(end_of(k), 1), m[1])[4] == 0) else None
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
        if k is not None and k is last_mark() and k[0] in 'WB':
            dd = sub(W, k[1])
            if isconst(dd):
                c = dd[-1]
                key = (k[0], 'W-pos=%s' % c)
                AUDIT[key] = AUDIT.get(key, 0) + 1
                if (k[0] == 'W' and c <= 1) or (k[0] == 'B' and c <= 3): AUDIT_EX.append((k[0], str(c)))
            else:
                import copy
                saved = (copy.deepcopy(GAMMA), copy.deepcopy(GAMMA_BY))
                sres = sign(addc(dd, -4), R)
                GAMMA[:] = saved[0]; GAMMA_BY.clear(); GAMMA_BY.update(saved[1])
                key = (k[0], 'var, W-pos-4 sign %s' % sres)
                AUDIT[key] = AUDIT.get(key, 0) + 1
                if sres != 1: AUDIT_EX.append((k[0], 'var', sres))
        if k is None:
            W = addc(W, 2); e = ['M', addc(W, -2)]; marks.append(e); return packet_back(addc(W, -2))
        if k[0] == 'M': k[0] = 'G'; return k
        if k[0] == 'W': k[0] = 'B'; return packet_back(k[1])
        if k[0] == 'B': k[0] = 'W'; k[1] = addc(k[1], 2); return packet_back(k[1])
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
                if d[4] < 0: raise Uncovered('gap overlaps marker')
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
                if isconst(d) and d[4] <= 2: return marks, W, meets, True      # the close: the round's rest is irrelevant
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
    if marks and marks[0][0] == 'M' and isconst(marks[0][1]) and marks[0][1][4] == 0:
        marks[0][0] = 'W'; marks[0][1] = form(0, 0, 0, 0, 1); extra = 4
    for m in marks: m[1] = addc(m[1], extra)
    W = addc(W, extra); marks.insert(0, ['G', form(0, 0, 0, 0, 1)])
    return marks, W, meets, False

def pred(d, kind): return half(addc(d, -2)) if kind == 'merge' else addc(half(d), 4)
LOOP = ['GWWW', 'GBW', 'GMB', 'GMWW', 'GMB', 'GMWW', 'GWWW', 'GBW']
def loop_prefix(hist):
    best = 0
    for ph in (0, 6):
        k = 0
        while k < len(hist) and hist[k] == LOOP[(ph + 1 + k) % 8]: k += 1     # hist[0] is the round after the start
        best = max(best, k)
    return best

def verify_leaf(kind, cos, rounds, shapes, run_claim, broken_claim, fin_claim):
    a, b, c, E = form(1), form(0, 1), form(0, 0, 1), form(0, 0, 0, 1)
    marks = [['G', form(0, 0, 0, 0, 1)], ['W', a], ['W', b], ['W', c]]; W = E
    lastD = None; lastKind = None; hist = []; chained = 0; broke_at = None
    for rd in range(1, rounds + 1):
        marks, W, meets, closed = run_round(marks, W, cos, None, None)
        if closed: return 'close with free R?!', None
        sh = ''.join(m[0] for m in marks); hist.append(sh)
        if sh != shapes[rd - 1]: return 'shape mismatch at round %d: %s vs %s' % (rd, sh, shapes[rd - 1]), None
        for d, k in meets:
            if lastD is not None and sub(pred(lastD, lastKind), d) != (0, 0, 0, 0, 0):
                if broke_at is None: broke_at = rd
            if broke_at is None: chained += 1
            lastD, lastKind = d, k
    fin = (len(marks) == 2 and marks[1][0] == 'M' and sub(marks[1][1], addc(W, -2)) == (0, 0, 0, 0, 0))
    if kind == 'pass':
        if rounds == 8 and loop_prefix(hist) == 8 and broke_at is None: return 'ok', chained
        return 'pass leaf does not complete the loop', chained
    # exit: the run must have broken in the last round, or the tape be clean there
    if broken_claim and broke_at != rounds: return 'break claimed at round %d, found %s' % (rounds, broke_at), chained
    if fin_claim and not fin: return 'clean tape claimed but not reached', chained
    if not broken_claim and not fin_claim: return 'exit with neither break nor clean tape', chained
    # no return to the loop after the loop prefix
    pre = loop_prefix(hist)
    for i in range(pre, len(hist)):
        for ph in range(8):
            j = 0
            while i + j < len(hist) and hist[i + j] == LOOP[(ph + j) % 8]: j += 1
            if j >= 4: return 'returns to 4 loop rounds after leaving', chained
    return 'ok', chained

# ---------- lattice helpers (4 dimensions) ----------
def hnf_cols(cols):
    M = [list(c) for c in cols]; rows = 4; basis = []
    for r in range(rows):
        M = [c for c in M if any(c[i] != 0 for i in range(r, rows))]
        while True:
            nz = [c for c in M if c[r] != 0]
            if len(nz) <= 1: break
            nz.sort(key=lambda c: abs(c[r])); piv = nz[0]
            for c in nz[1:]:
                q = c[r] // piv[r]
                for i in range(rows): c[i] -= q * piv[i]
        nz = [c for c in M if c[r] != 0]
        if nz:
            piv = nz[0]
            if piv[r] < 0: piv[:] = [-x for x in piv]
            basis.append(piv); M = [c for c in M if c is not piv]
        else: basis.append(None)
    return basis
def in_lattice(v, basis):
    v = list(v)
    for r in range(4):
        if basis[r] is None:
            if v[r] != 0: return False
            continue
        if v[r] % basis[r][r]: return False
        q = v[r] // basis[r][r]
        for i in range(4): v[i] -= q * basis[r][i]
    return all(x == 0 for x in v)
def cosets_intersect(c1, c2):
    cols = [[int(c1.B[i][k]) for i in range(4)] for k in range(4)] + [[int(c2.B[i][k]) for i in range(4)] for k in range(4)]
    return in_lattice([int(c1.x0[i] - c2.x0[i]) for i in range(4)], hnf_cols(cols))
def lattice_index(B):   # lower triangular
    p = 1
    for i in range(4): p *= abs(int(B[i][i]))
    return p

leaves = []
pat = re.compile(r'X pm=5 (\w+) bits=(\d+) run=(\d+) broken=(\d) fin=(\d) x0=(-?\d+),(-?\d+),(-?\d+),(-?\d+) B=([-\d,]+) rounds=(\d+) \| (.*)')
for line in open(sys.argv[1]):
    m = pat.match(line)
    if not m: continue
    kind, bits, run, br, fin = m.group(1), int(m.group(2)), int(m.group(3)), int(m.group(4)), int(m.group(5))
    x0 = [F(int(m.group(i))) for i in (6, 7, 8, 9)]; bl = [int(x) for x in m.group(10).split(',')]
    B = [[F(0)] * 4 for _ in range(4)]; t = 0
    for r in range(4):
        for c in range(r + 1): B[r][c] = F(bl[t]); t += 1
    leaves.append((kind, bits, run, br, fin, Coset(x0, B), int(m.group(11)), m.group(12).split()))
print('leaves:', len(leaves))
bad = 0; tot = F(0); maxchain = 0; und = unc = 0; passmass = F(0)
for kind, bits, run, br, fin, cos, rounds, shapes in leaves:
    if [int(x) % 2 for x in cos.x0] != [1, 0, 1, 0]: print('leaf outside the valid class'); bad += 1
    if lattice_index(cos.B) != 16 * 2 ** bits: print('index mismatch'); bad += 1
    tot += F(1, 2 ** bits)
    if kind == 'pass': passmass += F(1, 2 ** bits)
    try: res, ch = verify_leaf(kind, cos, rounds, shapes, run, br, fin)
    except Undecided as e: res, ch = 'undecided: %s' % e, 0; und += 1
    except Uncovered as e: res, ch = 'uncovered: %s' % e, 0; unc += 1
    if res != 'ok': print(kind, 'rounds', rounds, '->', res); bad += 1
    if kind == 'exit' and ch is not None: maxchain = max(maxchain, ch)
for i in range(len(leaves)):
    for j in range(i + 1, len(leaves)):
        if cosets_intersect(leaves[i][5], leaves[j][5]): print('leaves', i, j, 'intersect'); bad += 1
print('total measure', tot, '; pass measure', passmass, '=', float(passmass), '; leaf failures', bad, '; undecided', und, '; uncovered', unc)
print('most chained end meetings from the loop state before a break or a clean tape, over all exits:', maxchain)
print('every cone decision is exact once every gap exceeds', float(GAMMA[0]), 'cells')
for key in sorted(GAMMA_BY): print('   decisions involving gaps', key, 'are exact once those gaps exceed', float(GAMMA_BY[key]), 'cells')
print('CERTIFICATE', 'VALID' if bad == 0 and und == 0 and unc == 0 and tot == 1 else 'INVALID')
