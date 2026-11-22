"""Regions with symbolic eater phases: jump K super-cycles of an eater at once (K may be astronomically large);
the hit counts above the run of K emitted blocks become exact closed forms (sym.Sym)."""
import sys, copy, time
from fractions import Fraction
from lsa_ladder import *
from lsa_eater import supercycle, fuel_index
from lsa_region import Region
from lsa_sym import Sym, as_num
import geng
from geng import show, to_tokens, build

KMIN = 3
SCNEG = {}
LOG = [print]


def shape(toks):
    return tuple(('P', '*', t[2]) if type(t) is tuple and t[0] == 'P' and t[1] > 200 else t for t in toks)


def find_phase(btoks):
    """an eater super-cycle at the head of the bottom: (sc, E tokens, fuel index, rest tokens, K) or None"""
    fi = fuel_index(btoks[:16], thr=200)
    if fi is None:
        return None
    # the shape alone is enough to know a failure: the super-cycle search depends on the fuel only through its size
    for extra in range(0, 16):
        if fi + 1 + extra >= len(btoks):
            break
        E = btoks[:fi + 1 + extra]
        key = shape(E)
        if key in SCNEG:
            continue
        sc = supercycle(E, fi, Pmax=200000)
        if sc is None:
            SCNEG[key] = 1
            continue
        K = (E[fi][1] - sc['mmin']) // sc['dm'] + 1
        if K < KMIN:
            return None
        return sc, E, fi, btoks[fi + 1 + extra:], K
    return None


def block_map(sc, E):
    """the emitted block as levels, and its hit map f(x) = a x + b"""
    toks = list(sc['blk']) + list(E)
    bl, j = segment(toks, 0, 'h')
    if toks[j:] != list(E):
        return None
    vals = [chain([copy.copy(L) for L in bl], x) for x in (1, 2, 3, 1000)]
    a = vals[1] - vals[0]; b = vals[0] - a
    assert vals[2] == 3 * a + b and vals[3] == 1000 * a + b, vals
    return bl, a, b


def pass_positions(sc, E, fi):
    T = build(list(E), (('O', 0), None))
    pos = []
    for i in range(1, sc['P'] + 1):
        T = geng.h(T)
        o = to_tokens(T)[-1]
        assert o[0] == 'O'
        if o[1] > len(pos):
            pos.append(i)
    assert len(pos) == sc['c'], (pos, sc['c'])
    return pos


def G(K, Z, P, a, b):
    """hits into the top of [run of K blocks + region] until the region has had Z hits"""
    if K == 0:
        return Z
    if a == 1:
        return P + (Z + b) + (K - 1) * (P + b)
    e = a.bit_length() - 1
    assert a == 1 << e, "block multiplier not a power of 2"
    if isinstance(Z, Sym) or e * K > 10 ** 6:
        aK1 = Sym.pow2(e * (K - 1))
    else:
        aK1 = a ** (K - 1)
    I1 = aK1 * (a * Z + b) + (a * P + b) * (aK1 - 1) * Fraction(1, a - 1)
    r = P + I1
    return as_num(r) if isinstance(r, Sym) else (r if not isinstance(r, Fraction) else int(r))


def chain_sym(levels, H):
    if not isinstance(H, Sym):
        return chain([copy.copy(L) for L in levels], H)
    for L in levels:
        tail, cyc = L.path()
        assert sum(x[2] for x in cyc) == 1, "level passes more than one hit per cycle"
    x0 = 10 ** 6
    v = [chain([copy.copy(L) for L in levels], x) for x in (x0, x0 + 1, x0 + 2, 2 * x0)]
    A = v[1] - v[0]; B = v[0] - A * x0
    assert v[2] == A * (x0 + 2) + B and v[3] == A * 2 * x0 + B
    return as_num(A * H + B)


class PRegion(Region):
    depth = 0

    def step(self, maxbatch=10 ** 6):
        """run batches until an event ('event', top hits from now up to and including the event hit) or until an
        eater phase starts ('phase', ph)"""
        used0 = self.used
        nb = 0
        while nb < maxbatch:
            nb += 1
            bt = to_tokens(self.B)
            fi = fuel_index(bt[:16], thr=200)
            if fi is not None:
                key = shape(bt[:fi + 1])
                seen = getattr(self, 'seen', None)
                if seen is None:
                    seen = self.seen = {}
                if key in seen and bt[fi][1] < seen[key]:
                    ph = find_phase(bt)
                    if ph is not None and block_map(ph[0], ph[1]) is not None:
                        return 'phase', ph
                    if ph is not None:
                        LOG[0]('%s(block of the eater %s not regular: plain batches)' % ('  ' * self.depth, show(build(ph[1][:ph[2]], None))))
                        SCNEG[shape(ph[1])] = 1
                seen[key] = bt[fi][1]
            del bt
            u = self.used
            ev = self.feed(None, maxbatch=1)
            if ev != 'budget':
                return 'event', (u - used0) + ev      # feed counts from its own start
        return 'budget', None


FRAMES = []


def run_to_event(R):
    """top hits of the region R (from its present state) up to and including the hit of the next event"""
    frames = []
    while True:
        kind, x = R.step()
        if kind == 'budget':
            raise RuntimeError('budget')
        if kind == 'event':
            z = x
            break
        sc, E, fi, rest, K = x
        bl, a, b = block_map(sc, E)
        P = sc['P']; c = sc['c']
        LOG[0]('%sPHASE: eater %s with fuel %s: K = %s super-cycles of %d hits (fuel -%d, %d hits down, block x%d%+d)' % (
            '  ' * R.depth, show(build(E[:fi], None)), short(E[fi][1]), short(K), P, sc['dm'], c, a, b))
        fr = (R.used, [copy.copy(L) for L in R.levels], P, a, b)
        # the rest gets c hits per super-cycle, whatever it does with them (the eater never looks at it)
        geng.C[0] = 0
        W, done = geng.hpow(c * K, build(rest, None))
        del rest
        if done is not True:
            pos = pass_positions(sc, E, fi)
            j = done // c + 1; k = done % c
            LOG[0]('%s  event below the eater at its hit %d of cycle %s' % ('  ' * R.depth, pos[k], short(j)))
            frames.append(fr + (j - 1,))
            z = pos[k]
            break
        E2 = list(E); E2[fi] = ('P', E[fi][1] - sc['dm'] * K, E[fi][2])
        frames.append(fr + (K,))
        depth = R.depth + 1
        Q = R.Q
        R = None
        R = PRegion(E2 + to_tokens(W), Q=Q)
        del W
        R.depth = depth
    FRAMES[:] = frames
    for used, snap, P, a, b, K in reversed(frames):
        z = used + chain_sym(snap, G(K, z, P, a, b))
    return z


def short(n):
    s = str(n)
    return s if len(s) < 30 else '%s..(%d digits)' % (s[:10], len(s))
