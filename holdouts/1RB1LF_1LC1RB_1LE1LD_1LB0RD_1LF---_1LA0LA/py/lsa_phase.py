"""Regions with symbolic eater phases: jump K super-cycles of an eater at once (K may be astronomically large);
the hit counts above the run of K emitted blocks are exact while they fit in EXACT_BITS bits, then BigF."""
import sys, copy, time, math, pickle, os
from fractions import Fraction
from lsa_ladder import *
from lsa_eater import supercycle, fuel_index
from lsa_region import Region, prefix_tokens
import geng
from geng import show, to_tokens, build

KMIN = 3
SCNEG = {}
SCPOS = {}         # shape of an eater region -> its super-cycle (derived with the fuel symbolic, so valid for any fuel)
PFX = set()        # heads (shape up to the fuel) at which a phase was found: try at once when seen again
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
        sc = SCPOS.get(key)
        if sc is None:
            sc = supercycle(E, fi, Pmax=200000)
            if sc is not None:
                SCPOS[key] = sc
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
        while o[1] > len(pos):      # one hit can pass several hits down
            pos.append(i)
    assert len(pos) == sc['c'], (pos, sc['c'])
    return pos


EXACT_BITS = 10 ** 7   # numbers above this many bits are kept as BigF (a float mantissa and an exact exponent)


class BigF:
    """m * 2^E, 1 <= m < 2, E an exact (huge) integer: for counts far too large to write down"""
    __slots__ = ('m', 'E')

    def __init__(self, m, E):
        if m <= 0:
            raise ValueError(m)
        fe = math.frexp(m)
        self.m = fe[0] * 2; self.E = E + fe[1] - 1

    @staticmethod
    def of(x):
        if isinstance(x, BigF):
            return x
        x = Fraction(x)
        if x.denominator != 1:
            n, d = BigF.of(x.numerator), BigF.of(x.denominator)
            return BigF(n.m / d.m, n.E - d.E)
        x = int(x); n = x.bit_length()
        top = x >> max(0, n - 60)
        return BigF(float(top), max(0, n - 60))

    def mul(self, c):          # c: positive int, Fraction or BigF
        if isinstance(c, BigF):
            return BigF(self.m * c.m, self.E + c.E)
        c = Fraction(c)
        return BigF(self.m * (BigF.of(c.numerator).m / BigF.of(c.denominator).m),
                    self.E + BigF.of(c.numerator).E - BigF.of(c.denominator).E)

    def shl(self, e):
        return BigF(self.m, self.E + e)

    def add(self, o):          # o a BigF, or an int or Fraction (negative ones much smaller than self)
        if not isinstance(o, BigF) and o == 0:
            return self
        if not isinstance(o, BigF) and o < 0:
            o = BigF.of(-o)
            assert o.E + 2 < self.E
            d = self.E - o.E
            return self if d > 200 else BigF(self.m - o.m * 2.0 ** (-d), self.E)
        o = BigF.of(o) if not isinstance(o, BigF) else o
        if o.E > self.E:
            return o.add(self)
        d = self.E - o.E
        return self if d > 200 else BigF(self.m + o.m * 2.0 ** (-d), self.E)

    def log2(self):
        return self.E + math.log2(self.m)

    def log10(self):
        return self.log2() * math.log10(2)

    def __repr__(self):
        return '%.15g * 2^%d' % (self.m, self.E)


def big(x):
    return isinstance(x, BigF) or (isinstance(x, int) and x.bit_length() > EXACT_BITS)


def G(K, Z, P, a, b):
    """hits into the top of [run of K blocks + region] until the region has had Z hits"""
    if K == 0:
        return Z
    if a == 1:
        r = P + b + (K - 1) * (P + b)
        return Z.add(r) if isinstance(Z, BigF) else Z + r
    e = a.bit_length() - 1
    assert a == 1 << e, "block multiplier not a power of 2"
    if not big(Z) and e * K <= EXACT_BITS:
        aK1 = a ** (K - 1)
        I1 = aK1 * (a * Z + b) + Fraction((a * P + b) * (aK1 - 1), a - 1)
        r = P + I1
        assert r.denominator == 1
        return int(r)
    # a^(K-1) (a Z + b) + (a P + b)(a^(K-1) - 1)/(a - 1) + P, as a BigF
    Zb = BigF.of(Z).mul(a).add(b)
    return Zb.add(Fraction(a * P + b, a - 1)).shl(e * (K - 1))


def chain_sym(levels, H):
    """hits into the top of the levels until H hits reached the region below (an affine map of H)"""
    if not big(H):
        return chain([copy.copy(L) for L in levels], H)
    for L in levels:
        tail, cyc = L.path()
        assert sum(x[2] for x in cyc) == 1, "level passes more than one hit per cycle"
    x0 = 10 ** 6
    v = [chain([copy.copy(L) for L in levels], x) for x in (x0, x0 + 1, x0 + 2, 2 * x0)]
    A = v[1] - v[0]; B = v[0] - A * x0
    assert v[2] == A * (x0 + 2) + B and v[3] == A * 2 * x0 + B and A > 0
    return H.mul(A).add(B)


def unwind(frames, z):
    for used, snap, P, a, b, K in reversed(frames):
        z = chain_sym(snap, G(K, z, P, a, b))
        z = z.add(used) if isinstance(z, BigF) else z + used
        if isinstance(z, int) and z.bit_length() > EXACT_BITS:
            z = BigF.of(z)
    return z


BMC = {}


def block_map_c(sc, E):
    key = (shape(E), tuple(sc['blk']))
    if key not in BMC:
        BMC[key] = block_map(sc, E)
    return BMC[key]


class PRegion(Region):
    depth = 0
    fine = 0

    def step(self, maxbatch=10 ** 6):
        """run batches until an event ('event', top hits from now up to and including the event hit) or until an
        eater phase starts ('phase', ph)"""
        used0 = self.used
        nb = 0
        while nb < maxbatch:
            nb += 1
            bt, tail = prefix_tokens(self.B, 48)
            fi = fuel_index(bt[:16], thr=200)
            if fi is not None:
                key = shape(bt[:fi + 1])
                seen = getattr(self, 'seen', None)
                if seen is None:
                    seen = self.seen = {}
                if (key in seen and bt[fi][1] < seen[key]) or key in PFX or self.fine:
                    ph = find_phase(bt)
                    if ph is not None:
                        ph = ph[:3] + (build(ph[3], tail),) + ph[4:]
                    if ph is not None and block_map_c(ph[0], ph[1]) is not None:
                        PFX.add(key)
                        if self.fine:
                            self.Q, self.fine = self.fine_Q, 0
                        return 'phase', ph
                    if ph is not None:
                        LOG[0]('%s(block of the eater %s not regular at this hit: single hits)' % ('  ' * min(self.depth, 20), show(build(ph[1][:ph[2]], None))))
                        SCNEG[shape(ph[1])] = 1
                        if not self.fine:
                            # the super-cycle can start at any hit of the eater's cycle; find one where the block is regular
                            self.fine_Q, self.Q, self.fine = self.Q, 1, 4000
                seen[key] = bt[fi][1]
            del bt
            if self.fine:
                self.fine -= 1
                if not self.fine:
                    self.Q = self.fine_Q
            u = self.used
            ev = self.feed(None, maxbatch=1)
            if ev != 'budget':
                return 'event', (u - used0) + ev      # feed counts from its own start
        return 'budget', None


FRAMES = []


def save_state(path, R, frames, nph):
    st = dict(levels=R.levels, B=to_tokens(R.B), used=R.used, depth=R.depth, Q=R.Q, op=R.top_op,
              seen=getattr(R, 'seen', {}), frames=frames, nph=nph, SCPOS=SCPOS, SCNEG=SCNEG, PFX=PFX, TCACHE=TCACHE)
    with open(path + '.tmp', 'wb') as f:
        pickle.dump(st, f, protocol=4)
    os.replace(path + '.tmp', path)


def load_state(path):
    st = pickle.load(open(path, 'rb'))
    R = PRegion([], Q=st['Q'], op=st['op'])
    R.levels = st['levels']; R.B = build(st['B'], None); R.used = st['used']; R.depth = st['depth']
    R.seen = st['seen']
    SCPOS.update(st['SCPOS']); SCNEG.update(st['SCNEG']); PFX.update(st['PFX']); TCACHE.update(st.get('TCACHE', {}))
    return R, st['frames'], st['nph']


# ---------------------------------------------------------------- fast transitions between phases
# After a phase the word is E2 W: the eater with its leftover fuel, then the rest.  The way to the next phase only
# looks at the head of W up to the next big fuel F (count > BIGF); everything after F only receives hits.  So the
# transition is computed once with the part after F opaque (an ('O', r) token that counts the r hits it receives),
# checked to be the same for several values of F with the same residue mod MODF (F + d for d in SHIFTS, only the
# fuel's count moves), and then
# reused: the real tail receives its r hits with one hpow.  A transition that reads the opaque part, an event during
# the transition, or any mismatch falls back to the plain step.
TCACHE = {}
FAST = [True]
HOOK = [None]      # called with (phase number, sc, E, fuel index, rest, K) at each phase
BIGF = 10 ** 6
MODF = 4              # the transition may depend on F mod MODF (it does: the eater takes 4 units a round)
SHIFTS = (0, 4, 8, 12, 44, 4000)
TSTAT = dict(fast=0, slow=0, new=0, bad=0)


def head_split(W, n=400):
    pt, tail = prefix_tokens(W, n)
    for i, t in enumerate(pt):
        if type(t) is tuple and t[0] == 'P' and t[1] > BIGF:
            return pt[:i], pt[i], build(pt[i + 1:], tail)
    return None


def trans_run(E2, head, F, Q):
    try:
        R = PRegion(list(E2) + list(head) + [F], Q=Q, tail=(('O', 0), None))
        kind, x = R.step(maxbatch=600)
    except geng.Opaque:
        return None
    if kind != 'phase':
        return None
    sc, E, fi, rest, K = x
    rt = to_tokens(rest)
    if not rt or not (type(rt[-1]) is tuple and rt[-1][0] == 'O') or any(
            type(t) is tuple and t[0] == 'O' for t in list(E) + rt[:-1]):
        return None
    lv = [L.tokens() for L in R.levels]
    return dict(used=R.used, levels=R.levels, lvt=lv, sc=sc, E=list(E), fi=fi, rt=rt, K=K)


def _template(res, F):
    """the result with the one token that carries the fuel F (count F - s) marked; None if there is not exactly one"""
    out = []; s = None
    for part in ('E', 'rt'):
        for k, t in enumerate(res[part]):
            if type(t) is tuple and t[0] == 'P' and t[1] > BIGF:
                if s is not None:
                    return None
                s = (part, k, F[1] - t[1], t[2])
    return s


def trans_entry(E2, head, F, Q):
    ref = None
    for d in SHIFTS:
        Fd = ('P', F[1] + d, F[2])
        res = trans_run(E2, head, Fd, Q)
        if res is None:
            return False
        tm = _template(res, Fd)
        if tm is None:
            return False
        norm = (res['used'], res['lvt'], res['fi'], res['sc']['P'], res['sc']['dm'], res['sc']['c'], tm[0], tm[1], tm[2], tm[3],
                [t for k, t in enumerate(res['E']) if not (tm[0] == 'E' and k == tm[1])],
                [t for k, t in enumerate(res['rt']) if not (tm[0] == 'rt' and k == tm[1])])
        if ref is None:
            ref = (norm, res, tm)
        elif norm != ref[0]:
            return False
    return ref[1], ref[2]


def fast_next(E2, W, Q):
    """the next phase straight from (E2, W), or None (then use the plain step)"""
    hs = head_split(W)
    if hs is None:
        return None
    head, F, tail = hs
    key = (tuple(E2), tuple(head), F[2], F[1] % MODF)
    ent = TCACHE.get(key)
    if ent is None:
        TSTAT['new'] += 1
        ent = TCACHE[key] = trans_entry(E2, head, F, Q)
    if not ent:
        TSTAT['bad'] += 1
        return None
    res, (part, k, sh, w) = ent
    E = list(res['E']); rt = list(res['rt'])
    if part == 'E':
        E[k] = ('P', F[1] - sh, w)
    else:
        rt[k] = ('P', F[1] - sh, w)
    sc, fi = res['sc'], res['fi']
    K = (E[fi][1] - sc['mmin']) // sc['dm'] + 1
    if K < KMIN:
        return None
    geng.C[0] = 0
    W1, done = geng.hpow(rt[-1][1], tail)
    if done is not True:
        return None
    TSTAT['fast'] += 1
    return res['used'], [copy.copy(L) for L in res['levels']], (sc, E, fi, build(rt[:-1], W1), K)


def run_to_event(R, ckpt=None, every=200, frames=None, nph=0):
    """top hits of the region R (from its present state) up to and including the hit of the next event.
    ckpt: a file to save the state to every `every` phases (resume with load_state)"""
    frames = [] if frames is None else frames
    pending = None
    Q = R.Q
    while True:
        if pending is None:
            kind, x = R.step()
            if kind == 'budget':
                raise RuntimeError('budget')
            if kind == 'event':
                z = x
                break
            used, levels, depth = R.used, [copy.copy(L) for L in R.levels], R.depth
        else:
            used, levels, x, depth = pending
            pending = None
        sc, E, fi, rest, K = x
        bl, a, b = block_map_c(sc, E)
        P = sc['P']; c = sc['c']
        nph += 1
        LOG[0]('%sPHASE %d: eater %s with fuel %s: K = %s super-cycles of %d hits (fuel -%d, %d hits down, block x%d%+d)' % (
            '  ' * min(depth, 20), nph, show(build(E[:fi], None)), short(E[fi][1]), short(K), P, sc['dm'], c, a, b))
        fr = (used, levels, P, a, b)
        if HOOK[0]:
            HOOK[0](nph, sc, E, fi, rest, K)
        # the rest gets c hits per super-cycle, whatever it does with them (the eater never looks at it)
        geng.C[0] = 0
        W, done = geng.hpow(c * K, rest)
        del rest
        if done is not True:
            pos = pass_positions(sc, E, fi)
            j = done // c + 1; k = done % c
            LOG[0]('%s  event below the eater at its hit %d of cycle %s' % ('  ' * min(depth, 20), pos[k], short(j)))
            frames.append(fr + (j - 1,))
            z = pos[k]
            break
        E2 = list(E); E2[fi] = ('P', E[fi][1] - sc['dm'] * K, E[fi][2])
        frames.append(fr + (K,))
        R = None
        save = ckpt and (nph + 1) % every == 0
        nx = fast_next(E2, W, Q) if FAST[0] and not save else None
        if nx is not None:
            pending = (nx[0], nx[1], nx[2], depth + 1)
        else:
            TSTAT['slow'] += 1
            R = PRegion(E2, Q=Q, tail=W)
            R.depth = depth + 1
            if save:
                save_state(ckpt, R, frames, nph)
        del W
    FRAMES[:] = frames
    return unwind(frames, z)


def short(n):
    s = str(n)
    return s if len(s) < 30 else '%s..(%d digits)' % (s[:10], len(s))
