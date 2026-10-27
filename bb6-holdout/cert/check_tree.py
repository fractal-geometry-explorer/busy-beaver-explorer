"""Independent checker for a route-tree certificate (October 24).

The certificate is the leaf list of the route tree over two-marker states: every segment from the state
G 1, M m, M E - 2 (width E; m even, E odd) is followed, splitting the class of (m, E) whenever a digit test is not
decided, until the next clean tape, a cut at a depth limit, or a configuration the rules do not cover.  Each leaf line
    T <kind> bits <n> coset ... outs o1 o2 ... [forced f1 ...] | shape1 shape2 ...
claims the kind of ending, the list of meeting outcomes (d mod 4, in order) along the way, and the round shapes.

This program replays each leaf from the start state with its own implementation of the round recurrence on affine
forms in (m, E): a meeting outcome that the current class decides must agree with the recorded one, and one it does
not decide is imposed (a split); every comparison of positions is decided by the signs of its gap coefficients alone
(gaps m and E - m), and the checker refuses if they are mixed; every configuration outside the rules is a refusal.
It then checks that the split paths of all leaves form a complete prefix code (no path is a prefix of another and the
measures 2^-depth sum to 1), so the leaves partition the start class, and reports the phase-0 pass starts it met
along the paths with their sigma ceilings, recomputed from its own forms.

usage: python3 check_tree.py leaves.txt [--paths FILE]   (with --paths the split paths are also written out, so that a
       certificate checked in several pieces can have its partition verified over the union with kraft.py)
"""
import sys, re, math, os
from fractions import Fraction as F

# ---------- affine forms in (m, E): integer triples (cm, cE, c0), all scaled by SC = 2^96 ----------
SH = 96; SC = 1 << SH
def form(cm=0, cE=0, c0=0): return (cm * SC, cE * SC, c0 * SC)
def add(p, q): return (p[0] + q[0], p[1] + q[1], p[2] + q[2])
def sub(p, q): return (p[0] - q[0], p[1] - q[1], p[2] - q[2])
def addc(p, k): return (p[0], p[1], p[2] + k * SC)
def half(p):
    if (p[0] | p[1] | p[2]) & 1: raise Uncovered('halving past the scale')
    return (p[0] >> 1, p[1] >> 1, p[2] >> 1)
def isconst(p): return p[0] == 0 and p[1] == 0
def constval(p):     # the constant of a constant form, as an exact integer or Fraction
    return p[2] // SC if p[2] % SC == 0 else F(p[2], SC)

GAMMA = [0, 1]; GAMMA_BY = {}      # thresholds as (numerator, denominator)
def note_margin(gs, c):
    if (c < 0 and (gs[0] > 0 or gs[1] > 0)) or (c > 0 and (gs[0] < 0 or gs[1] < 0)):
        ac = -c if c < 0 else c; sg = abs(gs[0]) + abs(gs[1])
        if ac * GAMMA[1] > GAMMA[0] * sg: GAMMA[0], GAMMA[1] = ac, sg
        key = (1, 2) if (gs[0] and gs[1]) else ((1,) if gs[0] else (2,))
        old = GAMMA_BY.get(key, (0, 1))
        if ac * old[1] > old[0] * sg: GAMMA_BY[key] = (ac, sg)
def sign(p):
    """sign of a form on the cone of large gaps t1 = m, t2 = E - m; None if undecided"""
    cm, cE, c0 = p
    g1 = cm + cE; g2 = cE
    if g1 == 0 and g2 == 0: return (c0 > 0) - (c0 < 0)
    if g1 >= 0 and g2 >= 0: note_margin((g1, g2), c0); return 1
    if g1 <= 0 and g2 <= 0: note_margin((g1, g2), c0); return -1
    return None

class Undecided(Exception): pass
class Uncovered(Exception): pass
class Mismatch(Exception): pass

class Coset:
    """x = x0 + B y over (m, E); B lower triangular"""
    def __init__(self, x0, B, bits=0): self.x0 = list(x0); self.B = [list(r) for r in B]; self.bits = bits
    def eval(self, p):
        f0 = p[2] + p[0] * self.x0[0] + p[1] * self.x0[1]
        g = [p[0] * self.B[0][k] + p[1] * self.B[1][k] for k in range(2)]
        if f0 % SC or g[0] % SC or g[1] % SC: raise Undecided('non-integral')
        return f0 >> SH, [g[0] >> SH, g[1] >> SH]
    def residue(self, p, m):
        f0, g = self.eval(p)
        if any(x % m for x in g): raise Undecided('mod %d' % m)
        return f0 % m
    def decided4(self, p):
        """d mod 4 if the class decides it, else None (d must be even on the class)"""
        f0, g = self.eval(p)
        if f0 % 2 or any(x % 2 for x in g): raise Uncovered('odd distance')
        if any((x // 2) % 2 for x in g): return None
        return f0 % 4
    def impose(self, p, res):
        """restrict to d = res (mod 4); one binary digit"""
        f0, g = self.eval(p)
        h = [x // 2 for x in g]
        t = ((res - f0) // 2) % 2
        i = 0 if h[0] % 2 else 1
        assert h[i] % 2
        for r in range(2): self.x0[r] += t * self.B[r][i]
        for k in range(2):
            if k != i:
                for r in range(2): self.B[r][k] -= h[k] * self.B[r][i]
        for r in range(2): self.B[r][i] *= 2
        self.bits += 1
        # lower-triangular form (column operations) and a reduced x0
        B = self.B
        while B[0][1] != 0:
            if B[0][0] == 0 or abs(B[0][1]) < abs(B[0][0]):
                for r in range(2): B[r][0], B[r][1] = B[r][1], B[r][0]
                continue
            q = B[0][1] // B[0][0]
            for r in range(2): B[r][1] -= q * B[r][0]
        for c in range(2):
            if B[c][c] < 0:
                for r in range(2): B[r][c] = -B[r][c]
        for r in range(2):
            q = self.x0[r] // B[r][r]
            if q:
                for i2 in range(2): self.x0[i2] -= q * B[i2][r]

LEN = {'G': 3, 'M': 2, 'W': 2, 'B': 3}; VAL = {'G': 0, 'M': 1, 'W': 0, 'B': 1}

def run_round(marks, W, cos, outs, pos, splits):
    """one round of the mark rules; outs: the recorded outcomes, consumed from index pos[0]; splits: list that
    receives the outcomes imposed (the split path).  Returns (marks, W)."""
    marks = [[t, p] for t, p in marks]
    def less(p, q):
        s = sign(sub(p, q))
        if s is None: raise Undecided('order')
        return s < 0
    def sort_marks():
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
        if k is None: return None
        gap = sub(addc(end_of(k), 1), m[1])
        return k if (isconst(gap) and gap[2] == 0) else None
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
                    if constval(dd) < 3: raise Uncovered('block past the tape end')
                    if constval(dd) == 3: marks.remove(k); W = addc(W, -1); return packet_back(k[1])
                elif sign(addc(dd, -4)) != 1: raise Undecided('block at the tape end')
            k[0] = 'W'; k[1] = addc(k[1], 2); return packet_back(k[1])
        raise Uncovered('shift meets a sleeping gap')
    sort_marks()
    gap = marks[0]; guard = 0
    if gap[0] != 'G' or not (isconst(gap[1]) and gap[1][2] == SC): raise Uncovered('round does not start with the gap at 1')
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
                if d[2] < 0: raise Uncovered('gap overlaps marker')
                if d[2] <= 2 * SC: raise Uncovered('meeting at distance %s' % constval(d))
            else:
                s = sign(addc(d, -3))
                if s is None: raise Undecided('d sign')
                if s < 0: raise Uncovered('meeting at distance below 4')
            if pos[0] >= len(outs): raise Mismatch('more meetings than recorded outcomes')
            rec = outs[pos[0]]; pos[0] += 1
            r4 = cos.decided4(d)
            if r4 is None: cos.impose(d, rec); splits.append(rec); r4 = rec
            elif r4 != rec: raise Mismatch('recorded outcome %d, class gives %d' % (rec, r4))
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
            s = sign(sub(marks[i][1], end_of(marks[i - 1])))
            if s is None: raise Undecided('overlap test')
            if s <= 0: raise Uncovered('marks overlap')
    extra = 2
    if marks and marks[0][0] == 'M' and isconst(marks[0][1]) and marks[0][1][2] == 0:
        marks[0][0] = 'W'; marks[0][1] = form(0, 0, 1); extra = 4
    for m in marks: m[1] = addc(m[1], extra)
    W = addc(W, extra); marks.insert(0, ['G', form(0, 0, 1)])
    return marks, W

def lead(p):
    """the leading part of a form as a function of t = m/E: (coefficient of t, constant), constants dropped"""
    return (p[0] / SC, p[1] / SC)
def sigma_ceiling(b, c, E):
    best = -1e9; targ = 0
    lb, lc, lE = lead(b), lead(c), lead(E)
    for i in range(1025):
        t = i / 1024.0
        w = lE[0] * t + lE[1]; r = w - (lc[0] * t + lc[1]); l = 147 * (lb[0] * t + lb[1]) + 280 * w - 392 * (lc[0] * t + lc[1])
        if r <= 0: return 1e9, t
        if l == 0: continue
        sg = 3 * math.log2(w / r) + 2 * math.log2(abs(l) / w)
        if sg > best: best = sg; targ = t
    return best, targ

def verify_leaf(kind, outs, forced, shapes):
    """replay; returns (split path, list of (ceiling, depth at the pass start))"""
    cos = Coset([0, 1], [[2, 0], [0, 2]])
    marks = [['G', form(0, 0, 1)], ['M', form(1, 0, 0)], ['M', form(0, 1, -2)]]; W = form(0, 1, 0)
    pos = [0]; splits = []; entries = []; hist = []; pending = None
    for rd, sh in enumerate(shapes):
        marks, W = run_round(marks, W, cos, outs, pos, splits)
        got = ''.join(m[0] for m in marks)
        if got != sh: raise Mismatch('shape at round %d: %s claimed, %s derived' % (rd + 1, sh, got))
        hist.append(got)
        if got == 'GWWW': pending = (marks[2][1], marks[3][1], W, len(splits))
        if len(hist) >= 3 and hist[-3:] == ['GWWW', 'GBW', 'GMB'] and pending is not None:
            b, c, E, depth = pending; sg, t = sigma_ceiling(b, c, E); entries.append((sg, depth, t)); pending = None
    if pos[0] != len(outs): raise Mismatch('%d recorded outcomes, %d meetings replayed' % (len(outs), pos[0]))
    if kind == 'clean':
        alive = marks
        if not (len(alive) in (2, 3) and alive[-1][0] == 'M' and sub(alive[-1][1], addc(W, -2)) == (0, 0, 0)):
            raise Mismatch('not a clean tape at the end')
    elif kind in ('cut', 'overflow'):      # undecided at the depth limit, or dropped at a coefficient overflow: both are counted as undecided
        splits = splits + list(forced)
    else:
        raise Mismatch('unknown kind ' + kind)
    return splits, entries

pat = re.compile(r'^T (\w+) bits (\d+) coset (\S+) (\S+) (\S+) (\S+) (\S+)( code -?\d+)? outs([ \d]*?)(?: forced([ \d]+))? \| (.*)$')
paths = []; total = F(0); bad = 0; und = 0; unc = 0; nleaf = 0
hist_c = {}; mass_c = {}; top = (-1, None); meas_entries = F(0); kinds = {}
mass_k = {}
PATHS = open(sys.argv[sys.argv.index('--paths') + 1], 'w') if '--paths' in sys.argv else None
for line in open(sys.argv[1]):
    if not line.startswith('T '): continue
    m = pat.match(line.rstrip('\n'))
    if not m: print('unparsed:', line[:100]); bad += 1; continue
    kind = m.group(1); bits = int(m.group(2))
    outs = [int(x) for x in m.group(9).split()]; forced = [int(x) for x in (m.group(10) or '').split()]
    shapes = m.group(11).split()
    nleaf += 1; kinds[kind] = kinds.get(kind, 0) + 1
    try:
        splits, entries = verify_leaf(kind, outs, forced, shapes)
        depth = len(splits)
        claimed = bits + len(forced)
        if depth != claimed: raise Mismatch('depth %d derived, %d claimed' % (depth, claimed))
        code = ''.join('1' if s else '0' for s in splits)
        paths.append(code); total += F(1, 2 ** depth)
        if PATHS: PATHS.write(code + '\n')
        w = F(1, 2 ** depth); mass_k[kind] = mass_k.get(kind, F(0)) + w
        for sg, edepth, t in entries:
            bkt = int(math.floor(sg)) if sg < 1e8 else 999
            hist_c[bkt] = hist_c.get(bkt, 0) + 1; mass_c[bkt] = mass_c.get(bkt, F(0)) + w; meas_entries += w
            if sg > top[0]: top = (sg, (edepth, t, kind, len(shapes)))
    except Undecided as e: print('leaf', nleaf, kind, 'undecided:', e); und += 1
    except Uncovered as e: print('leaf', nleaf, kind, 'uncovered:', e); unc += 1
    except Mismatch as e: print('leaf', nleaf, kind, 'MISMATCH:', e); bad += 1
    if nleaf % 20000 == 0: print('...', nleaf, 'leaves', file=sys.stderr)
print('leaves:', nleaf, kinds)
print('measure by kind:', {k: '%.4e' % float(v) for k, v in mass_k.items()})
print('replay failures:', bad, '; undecided:', und, '; uncovered:', unc)
# complete prefix code?
paths.sort()
prefix_bad = 0
for i in range(1, len(paths)):
    if paths[i].startswith(paths[i - 1]) : prefix_bad += 1
dup = len(paths) - len(set(paths))
print('split paths: %d; total measure %s; one path a prefix of the next: %d; duplicates: %d' % (len(paths), float(total), prefix_bad, dup))
print('phase-0 plain entries met along the paths: measure %.6e (summed over the leaves below each); largest ceiling %.3f' % (float(meas_entries), top[0]))
print('  by ceiling (floor): ' + ' '.join('%d:%.4e/%d' % (k, float(mass_c[k]), hist_c[k]) for k in sorted(hist_c)))
print('every cone decision is exact once every gap exceeds', GAMMA[0] / GAMMA[1], 'cells')
for key in sorted(GAMMA_BY): print('   decisions involving gaps', key, 'are exact once those gaps exceed', GAMMA_BY[key][0] / GAMMA_BY[key][1], 'cells')
ok = bad == 0 and und == 0 and unc == 0 and prefix_bad == 0 and dup == 0 and total == 1
print('CERTIFICATE VALID' if ok else 'CERTIFICATE NOT VERIFIED')
