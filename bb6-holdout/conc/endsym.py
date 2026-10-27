"""Exact endgame of a loop pass start (October 22).

From a phase-0 pass start G 1, W a, W b, W c with end E and R = E - c - 1 held fixed (small), the left positions
a, b and the width E are free: every position is an affine form in (a, b, E) with a concrete far-apart value used
only to order marks.  One round follows the stepper's engine (stepper/engine.js) step for step, including every
check it makes for cases the proven rules do not cover.  Every test of a position's low bits that the current
residue class does not decide splits the class in two, so each path is a residue class of (a, b, E) of exact density
2^-bits.  A path stops when the gap comes within 2 of the end marker (close), a packet reaches a block (halt), the
end-meeting chain breaks with the end far away, a new phase-0 pass starts (then this was not the last pass start),
or the engine flags an uncovered case.

usage: python3 endsym.py Rmin Rmax [geometry] [step]   -> one line per R and a summary
"""
import sys
from fractions import Fraction as F

NV = 3                       # variables a, b, E
LEN = {'G': 3, 'M': 2, 'W': 2, 'B': 3}
VAL = {'G': 0, 'M': 1, 'W': 0, 'B': 1}


class Pos:
    __slots__ = ('f', 'v')
    def __init__(self, f, v): self.f = tuple(f); self.v = v
    def __add__(self, o):
        if isinstance(o, Pos): return Pos([x + y for x, y in zip(self.f, o.f)], self.v + o.v)
        f = list(self.f); f[-1] += o; return Pos(f, self.v + o)
    def __sub__(self, o):
        if isinstance(o, Pos): return Pos([x - y for x, y in zip(self.f, o.f)], self.v - o.v)
        return self + (-o)
    def half(self): return Pos([x / 2 for x in self.f], self.v / 2)
    def lin0(self): return all(x == 0 for x in self.f[:-1])
    def const(self): return self.f[-1]


def cpos(c): return Pos([F(0)] * NV + [F(c)], F(c))


class Branch(Exception): pass
class Inconsistent(Exception): pass


class Coset:
    """x = x0 + B y over integer y; tests of a form's parity either follow or split the coset."""
    def __init__(self, x0, B): self.x0 = list(x0); self.B = [r[:] for r in B]; self.bits = 0
    def copy(self):
        c = Coset(self.x0, self.B); c.bits = self.bits; return c
    def ev(self, form):
        f0 = form[NV] + sum(form[i] * self.x0[i] for i in range(NV))
        g = [sum(form[i] * self.B[i][k] for i in range(NV)) for k in range(NV)]
        if f0.denominator != 1 or any(x.denominator != 1 for x in g): raise Inconsistent('form not integral on the class')
        return int(f0), [int(x) for x in g]
    def mod2(self, form, ctx):
        f0, g = self.ev(form)
        odd = [k for k in range(NV) if g[k] % 2]
        if not odd: return f0 % 2
        if ctx.fi < len(ctx.forced): r = ctx.forced[ctx.fi]; ctx.fi += 1
        else: raise Branch()
        i = odd[0]; t = (r - f0) % 2
        for row in range(NV): self.x0[row] += t * self.B[row][i]
        for k in range(NV):
            if k != i:
                for row in range(NV): self.B[row][k] -= g[k] * self.B[row][i]
        for row in range(NV): self.B[row][i] *= 2
        self.bits += 1
        return r


def sign(p):                 # sign of a position difference: forms with a variable part are far from 0
    if p.lin0(): c = p.const(); return (c > 0) - (c < 0)
    return (p.v > 0) - (p.v < 0)
def iszero(p): return p.lin0() and p.const() == 0
def endOf(m): return m['p'] + (LEN[m['t']] - 1)


class Stop(Exception):
    def __init__(self, k, text=''): self.k = k; self.text = text


def do_round(st, cos, ctx):
    """st: dict W (Pos), marks (list of {t, p}), lastD, lastKind, chain. Returns new state and the end meetings."""
    W = st['W']
    marks = sorted([{'t': m['t'], 'p': m['p']} for m in st['marks']], key=lambda m: m['p'].v)
    meets = []
    lastD, lastKind, chain = st['lastD'], st['lastKind'], st['chain']

    def firstRight(x):
        r = None
        for m in marks:
            if m['p'].v > x.v and (r is None or m['p'].v < r['p'].v): r = m
        return r
    def lastMark(): return max(marks, key=lambda m: m['p'].v)
    def leftNeighbour(m):
        r = None
        for k in marks:
            if k is not m and k['p'].v < m['p'].v and (r is None or k['p'].v > r['p'].v): r = k
        return r
    def touchesLeft(m):
        k = leftNeighbour(m)
        return k if (k is not None and iszero(endOf(k) + 1 - m['p'])) else None
    def remove(m):
        for i, k in enumerate(marks):
            if k is m: del marks[i]; return
    def packetBack(x):
        nonlocal W
        b = None
        for m in marks:
            if m['p'].v < x.v and m['t'] != 'M' and (b is None or m['p'].v > b['p'].v): b = m
        crossed = sorted([m for m in marks if m['t'] == 'M' and m['p'].v < x.v and (b is None or m['p'].v > b['p'].v)],
                         key=lambda m: m['p'].v, reverse=True)
        for m in crossed:
            k = touchesLeft(m)
            if k is not None and k['t'] == 'W': raise Stop('uncovered', 'packet meets marker after wall')
            if k is not None and k['t'] == 'G': raise Stop('unbuilt', 'packet meets marker after gap')
        if b is None: return None
        if b['t'] == 'B': raise Stop('halt')
        if b['t'] == 'G': b['p'] = b['p'] + 2; return b
        k = touchesLeft(b)
        if k is not None and VAL[k['t']] == 0: raise Stop('uncovered', 'packet meets wall with a 0-mark on its left')
        q = b['p']; b['t'] = 'M'; b['p'] = q - 1; g = {'t': 'G', 'p': q + 1}; marks.append(g); return g
    def shiftFrom(x):
        nonlocal W
        k = firstRight(x)
        if k is None:
            W = W + 2; e = {'t': 'M', 'p': W - 2}; marks.append(e); return packetBack(W - 2)
        if k['t'] == 'M': k['t'] = 'G'; return k
        if k['t'] == 'W': k['t'] = 'B'; return packetBack(k['p'])
        if k['t'] == 'B': k['t'] = 'W'; k['p'] = k['p'] + 2; return packetBack(k['p'])
        raise Stop('broken', 'shift meets a sleeping gap')

    gap = marks[0]; guard = 0
    while gap is not None:
        guard += 1
        if guard > 10000: raise Stop('broken', 'round too long')
        g = gap['p']; m = firstRight(g)
        kl = touchesLeft(gap)
        if kl is not None and VAL[kl['t']] == 0: raise Stop('uncovered', 'gap with a 0-mark on its left')
        if m is None:
            remove(gap); W = W + 3; e = {'t': 'M', 'p': W - 2}; marks.append(e); gap = packetBack(W - 2)
        elif m['t'] == 'M':
            d = m['p'] - g - 3
            if sign(d) < 0: raise Stop('broken', 'gap overlaps marker')
            if cos.mod2(d.f, ctx) != 0: raise Stop('broken', 'odd distance')
            isEnd = m is lastMark()
            q = cos.mod2(d.half().f, ctx)        # d/2 mod 2: 0 swap, 1 merge
            if isEnd:
                kind = 'swap' if q == 0 else 'merge'
                if lastD is not None:
                    pr = (lastD - 2).half() if lastKind == 'merge' else lastD.half() + 4
                    chain = chain + 1 if iszero(d - pr) else 1
                else: chain = 1
                meets.append((d, kind, chain))
                if chain == 1 and lastD is not None and not d.lin0() and not NOBREAK:
                    raise Stop('break', d)
                lastD, lastKind = d, kind
                if sign(d - 2) <= 0: raise Stop('close', d)
            if q == 0:
                h = d.half(); m['p'] = g + h - 1; gap['p'] = g + h + 1
            else:
                remove(gap); m['t'] = 'W'; m['p'] = g + d.half() + 3; gap = packetBack(m['p'])
        elif m['t'] == 'W':
            x = m['p']; remove(gap); remove(m); gap = shiftFrom(x)
        elif m['t'] == 'B':
            m['t'] = 'W'; m['p'] = m['p'] - 1; gap = shiftFrom(m['p'])
        else:
            raise Stop('broken', 'gap meets a sleeping gap')
        marks.sort(key=lambda m: m['p'].v)
        for i in range(1, len(marks)):
            if sign(marks[i]['p'] - endOf(marks[i - 1])) <= 0: raise Stop('broken', 'marks overlap')
    extra = 2
    if marks and marks[0]['t'] == 'M' and iszero(marks[0]['p']):
        marks[0]['t'] = 'W'; marks[0]['p'] = cpos(1); extra = 4
    for mk in marks: mk['p'] = mk['p'] + extra
    W = W + extra; marks.insert(0, {'t': 'G', 'p': cpos(1)})
    check_tape(W, marks, cos, ctx)
    return {'W': W, 'marks': marks, 'lastD': lastD, 'lastKind': lastKind, 'chain': chain}, meets


def check_tape(W, marks, cos, ctx):
    ms = sorted(marks, key=lambda m: m['p'].v)
    f = ms[0]
    if sign(f['p']) < 0: raise Stop('uncovered', 'mark left of 0')
    if iszero(f['p']):
        if VAL[f['t']] == 0: raise Stop('uncovered', '0-mark at cell 0')
    elif (cos.mod2(f['p'].f, ctx) == 1) != (VAL[f['t']] == 0): raise Stop('uncovered', 'first mark off the stripes')
    for i in range(1, len(ms)):
        a, b = ms[i - 1], ms[i]; L = b['p'] - endOf(a) - 1
        s = sign(L)
        if s < 0: raise Stop('uncovered', 'overlap')
        if s == 0:
            if VAL[a['t']] == VAL[b['t']]: raise Stop('uncovered', 'marks touch')
        elif (cos.mod2(L.f, ctx) == 1) != (VAL[a['t']] == VAL[b['t']]): raise Stop('uncovered', 'stripe length')
    l = ms[-1]; T = W - 1 - endOf(l); s = sign(T)
    if s < 0: raise Stop('uncovered', 'past the width')
    if s == 0:
        if VAL[l['t']] == 0: raise Stop('uncovered', 'last cell not a 1')
    elif (cos.mod2(T.f, ctx) == 1) != (VAL[l['t']] == 0): raise Stop('uncovered', 'end stripes')


class Ctx:
    def __init__(self, forced): self.forced = forced; self.fi = 0


PHASE0 = True
NOBREAK = False
START = None
CLOSES = []
PASSES = []
GEOS = [(F(1559396385), F(6743276446), F(10395969088)), (F(1000), F(5000), F(10000)), (F(3000), F(9000), F(10000)),
        (F(100), F(9500), F(10000)), (F(2000), F(7600), F(10000))]


def search(R, geo=0, cut=60, maxr=120):
    SC = F(2) ** 200
    av, bv, Ev = (x * SC for x in GEOS[geo])
    var = lambda i, v: Pos([F(int(i == j)) for j in range(NV)] + [F(0)], v)
    a, b, E = var(0, av), var(1, bv), var(2, Ev)
    c = E - (R + 1)
    st0 = {'W': E, 'marks': [{'t': 'G', 'p': cpos(1)}, {'t': 'W', 'p': a}, {'t': 'W', 'p': b}, {'t': 'W', 'p': c}],
           'lastD': None, 'lastKind': None, 'chain': 0}
    if START is not None: st0 = START()
    out = {}
    def rec(key, w, extra=None):
        o = out.setdefault(key, [F(0), 0, []]); o[0] += w; o[1] += 1
        if extra is not None and len(o[2]) < 6: o[2].append(extra)
    # the start class: all parities, the initial tape check decides which are real
    roots = []
    for pa in (0, 1):
        for pb in (0, 1):
            for pE in (0, 1):
                cs = Coset([pa, pb, pE], [[2 * (i == j) for j in range(NV)] for i in range(NV)])
                try: check_tape(st0['W'], st0['marks'], cs, Ctx([]))
                except Stop: continue
                roots.append(cs)
    stack = [(st0, cs, [], [], 0, None) for cs in roots]
    while stack:
        st, cs, forced, shapes, nmeet, g4 = stack.pop()
        c2 = cs.copy(); ctx = Ctx(forced)
        try:
            nx, meets = do_round(st, c2, ctx)
        except Branch:
            if cs.bits + len(forced) + 1 > cut: rec('cut', F(1, 2 ** (cs.bits + len(forced))))
            else:
                stack.append((st, cs, forced + [0], shapes, nmeet, g4)); stack.append((st, cs, forced + [1], shapes, nmeet, g4))
            continue
        except Stop as s:
            w = F(1, 2 ** c2.bits); nm = nmeet + (0 if s.k != 'close' else 1)
            if s.k == 'close':
                rec('close', w, (int(s.text.const()), nmeet + 1, len(shapes) + 1)); CLOSES.append((R, list(c2.x0), [r[:] for r in c2.B], shapes + ['(close)']))
            elif s.k == 'break': rec('break', w)
            else: rec(s.k, w, (s.text, len(shapes) + 1))
            continue
        except Inconsistent as e:
            rec('inconsistent', F(1, 2 ** c2.bits), str(e)); continue
        sh = ''.join(m['t'] for m in sorted(nx['marks'], key=lambda m: m['p'].v))
        shapes2 = shapes + [sh]; L = len(shapes2)
        if PHASE0 and ((L == 1 and sh != 'GBW') or (L == 2 and sh != 'GMB')):
            rec('notphase0', F(1, 2 ** c2.bits), sh); continue
        if L >= 3 and shapes2[L - 3:] == ['GWWW', 'GBW', 'GMB']:
            Rn = g4['W'] - max(g4['marks'], key=lambda m: m['p'].v)['p'] - 1
            rec('pass', F(1, 2 ** c2.bits), (int(Rn.const()) if Rn.lin0() else 'far', L - 3)); PASSES.append((R, list(c2.x0), [r[:] for r in c2.B])); continue
        if L > maxr: rec('limit', F(1, 2 ** c2.bits), ' '.join(shapes2[:20])); continue
        stack.append((nx, c2, [], shapes2, nmeet + len(meets), nx if sh == 'GWWW' else g4))
    return out


if __name__ == '__main__':
    R0, R1 = int(sys.argv[1]), int(sys.argv[2]); geo = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    step = int(sys.argv[4]) if len(sys.argv) > 4 else 2
    closing = []
    for R in range(R0, R1 + 1, step):
        out = search(R, geo)
        tot = sum(v[0] for v in out.values())
        parts = ', '.join(f"{k} {float(v[0]):.3g} ({v[1]})" for k, v in sorted(out.items()))
        line = f"R {R}: total {float(tot):.6f}; {parts}"
        if 'close' in out: line += '; close examples (d, meetings, rounds): ' + str(out['close'][2]); closing.append(R)
        for k in out:
            if k not in ('close', 'break', 'cut') and out[k][2]: line += f'; {k}: {out[k][2][:2]}'
        print(line, flush=True)
    print('R values with a close:', closing)
