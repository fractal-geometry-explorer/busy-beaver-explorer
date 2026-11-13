"""Block-level macro machine for 1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---, with any pattern of bounces.

The tape between two left records is a list of words, each a token list with its own parameter t (a P-block
(10)^D x at a record, its images later); the head sits between a left stack and a right stack of words, in a
situation: moving right, ('R', q, u) with u the K cells left of the head; moving left, ('L', q, v) with v the
cells right of the head (at most KR).  On the blank side (nothing frozen on the left) the right-moving situation is
('RB', q, cells, off): the left of the head is 0^inf followed by `cells`, the record's start cell `off` cells from
their left end.  Every crossing of a word (kind = its token list) from a situation is found once by a symbolic run
(bbtools.symtm) and cached.
"""
import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../../tools/py'))
from bbtools import symtm
from bbtools.symtm import Config, Ctx, Rep, Blank, TouchContext, Lin
from bbtools.machine import Machine

MACH = '1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---'
M = Machine.parse(MACH)
ST = 'ABCDEF'
K = 8
KR = 1000
DMIN = 8
T = Lin('t')


class Fail(Exception):
    pass


def block_kind(D, x):
    """The word of a P-block (10)^D x: (kind tokens, t)."""
    if D < DMIN:
        return tuple([1, 0] * D + [x]), 0
    t = (D - DMIN) // 2
    if (D - DMIN) % 2 == 0:
        return (Rep((1, 0, 1, 0), T + DMIN // 2), x), t
    return (1, 0, Rep((1, 0, 1, 0), T + DMIN // 2), x), t


def take_back(toks, k):
    toks = list(toks)
    out = []
    while len(out) < k:
        if not toks:
            raise Fail('not enough cells')
        z = toks[-1]
        if isinstance(z, int):
            out.append(toks.pop())
        elif isinstance(z, Rep):
            if z.n.is_zero():
                toks.pop(); continue
            if not z.n.surely_ge(1):
                raise Fail('rep may be empty: %r' % (z,))
            toks.pop()
            if not (z.n - 1).is_zero():
                toks.append(Rep(z.word, z.n - 1))
            toks.extend(z.word)
        else:
            raise Fail('context in word')
    return tuple(toks), tuple(reversed(out))


def take_front(toks, k):
    toks = list(toks)
    out = []
    while len(out) < k and toks:
        z = toks[0]
        if isinstance(z, int):
            out.append(toks.pop(0))
        elif isinstance(z, Rep):
            if z.n.is_zero():
                toks.pop(0); continue
            if not z.n.surely_ge(1):
                break
            toks.pop(0)
            rest = [Rep(z.word, z.n - 1)] if not (z.n - 1).is_zero() else []
            toks[0:0] = list(z.word) + rest
        else:
            break
    return tuple(out), tuple(toks)


def ncells(toks):
    n = Lin(0)
    for z in toks:
        if isinstance(z, int):
            n = n + 1
        elif isinstance(z, Rep):
            n = n + len(z.word) * z.n
    return n


def about_to_enter_left(c):
    if not c.left or not isinstance(c.left[-1], Ctx) or not c.right:
        return False
    z = c.right[0]
    if isinstance(z, Rep):
        if not z.n.surely_ge(1):
            return False
        z = z.word[0]
    if not isinstance(z, int):
        return False
    tr = M.table[c.state][z]
    return tr is not None and tr[1] != 1


def srun(cfg, off, maxm=50000):
    """Run until 'L' (about to move left into the context L), 'R' (reading the context R), 'rec' (off not None:
    state B left of the start cell), 'halt'.  Returns (why, off_now)."""
    tot0 = ncells(cfg.left[1:] + cfg.right[:-1])
    st = {'off': off}

    def stop(c):
        if off is None:
            return about_to_enter_left(c)
        d = ncells(c.left[1:] + c.right[:-1]) - tot0
        if not d.is_const():
            raise Fail('created not constant')
        o = off + d.k
        st['off'] = o
        if c.state != 1:
            return False
        nl = ncells(c.left[1:])
        if nl.is_const():
            return nl.k < o
        if nl.k >= o and all(a > 0 for a in nl.c.values()):
            return False
        raise Fail('record test undecided %r %r' % (nl, o))
    try:
        symtm.run(M, cfg, stop, max_moves=maxm, rotate=True)
    except TouchContext as e:
        return str(e), st['off']
    except symtm.Halted:
        return 'halt', st['off']
    except symtm.NeedSplit as e:
        raise Fail('split %s at %s' % (e, cfg))
    if off is None:
        return 'L', None
    return 'rec', st['off']


def strip0(cells):
    cells = list(cells)
    if not all(isinstance(z, int) for z in cells):
        raise Fail('record left part not literal: %r' % (cells,))
    while cells and cells[0] == 0:
        cells.pop(0)
    return tuple(cells)


# ------------------------------------------------------------------ transitions (cached)
CFGS = {}  # key -> (start config, end config) of each symbolic run
CR = {}   # right-moving crossings
CL = {}   # left-moving crossings
STATS = {'runs': 0}


def cross_right(sig, kind):
    """sig ('R', q, u) or ('RB', q, cells, off); kind: the word on the right.  Results:
    ('pass', sig2, W, steps, offW)  W frozen on the left (offW not None: it sits on the blank side)
    ('turn', lam, V, steps)          V pushed on the right
    ('rec', ell, right tokens, steps)
    ('halt', cfg)"""
    key = (sig, kind)
    if key in CR:
        return CR[key]
    STATS['runs'] += 1
    if sig[0] == 'R':
        _, q, u = sig
        cfg = Config([Ctx('L')] + list(u), q, list(kind) + [Ctx('R')])
        off = None
    else:
        _, q, cells, off = sig
        cfg = Config([Blank()] + list(cells), q, list(kind) + [Ctx('R')])
    c0 = cfg.copy()
    why, o = srun(cfg, off)
    CFGS[('R',) + key] = (c0, cfg.copy(), why)
    if why == 'R':
        left = cfg.left[1:]
        if off is None:
            rest, u2 = take_back(left, K)
            res = ('pass', ('R', cfg.state, u2), rest, cfg.steps, None)
        else:
            try:
                rest, u2 = take_back(left, K)
                if not rest:
                    raise Fail('empty')
                res = ('pass', ('R', cfg.state, u2), rest, cfg.steps, o)
            except Fail:
                if not all(isinstance(z, int) for z in left):
                    raise
                res = ('pass', ('RB', cfg.state, tuple(left), o), (), cfg.steps, None)
    elif why == 'L':
        v, rest = take_front(cfg.right[:-1], KR)
        res = ('turn', ('L', cfg.state, v), rest, cfg.steps)
    elif why == 'rec':
        res = ('rec', strip0(cfg.left[1:]), tuple(cfg.right[:-1]), cfg.steps)
    elif why == 'halt':
        res = ('halt', cfg)
    else:
        raise Fail('cross_right %r %r: %s at %s' % (sig, kind, why, cfg))
    CR[key] = res
    return res


def cross_left(lam, kind, off):
    """lam ('L', q, v); kind: the word on the left (off not None: it sits on the blank side).  Results:
    ('pass', lam2, V, steps)        V pushed on the right
    ('turn', sig, W, steps, offW)   the head turned right; W stays on the left (offW: on the blank side)
    ('rec', ell, right tokens, steps)"""
    key = (lam, kind, off)
    if key in CL:
        return CL[key]
    STATS['runs'] += 1
    _, q, v = lam
    cfg = Config(([Ctx('L')] if off is None else [Blank()]) + list(kind), q, list(v) + [Ctx('R')])
    c0 = cfg.copy()
    why, o = srun(cfg, off)
    CFGS[('L',) + key] = (c0, cfg.copy(), why)
    if why == 'L':
        v2, rest = take_front(cfg.right[:-1], KR)
        res = ('pass', ('L', cfg.state, v2), rest, cfg.steps)
    elif why == 'R':
        left = cfg.left[1:]
        if off is None:
            rest, u = take_back(left, K)
            res = ('turn', ('R', cfg.state, u), rest, cfg.steps, None)
        else:
            try:
                rest, u = take_back(left, K)
                if not rest:
                    raise Fail('empty')
                res = ('turn', ('R', cfg.state, u), rest, cfg.steps, o)
            except Fail:
                if not all(isinstance(z, int) for z in left):
                    raise
                res = ('turn', ('RB', cfg.state, tuple(left), o), (), cfg.steps, None)
    elif why == 'rec':
        res = ('rec', strip0(cfg.left[1:]), tuple(cfg.right[:-1]), cfg.steps)
    elif why == 'halt':
        res = ('halt', cfg)
    else:
        raise Fail('cross_left %r %r: %s at %s' % (lam, kind, why, cfg))
    CL[key] = res
    return res


CMIN = 2


def normalize(kind, t):
    """Re-parametrize a word so that every repeat with t has count >= CMIN (t -> t + m), or make it literal."""
    cs = [z.n.k for z in kind if isinstance(z, Rep) and z.n.c]
    if not cs:
        return kind, 0
    m = max(0, CMIN - min(cs))
    if m == 0:
        return kind, t
    if t >= m:
        sh = {'t': 1}
        out = []
        for z in kind:
            if isinstance(z, Rep) and z.n.c:
                out.append(Rep(z.word, z.n + m * z.n.c.get('t', 0)))
            else:
                out.append(z)
        return tuple(out), t - m
    out = []
    for z in kind:
        if isinstance(z, Rep):
            n = z.n.subs({'t': t}) if z.n.c else z.n.k
            out.extend(list(z.word) * n)
        else:
            out.append(z)
    return tuple(out), 0


# ------------------------------------------------------------------ concrete macro step
def ev(st, t):
    return st.subs({'t': t}) if st.c else st.k


def subst(toks, t):
    out = []
    for z in toks:
        if isinstance(z, Rep):
            n = z.n.subs({'t': t}) if z.n.c else z.n.k
            if n < 0:
                raise Fail('negative count')
            if n:
                out.append((z.word, n))
        else:
            out.append(z)
    return out


def macro_step(ell, c0, blocks, trace=None):
    """The record 0^inf ell B> c0 enc(blocks).  Returns ((ell', c', blocks'), steps, info)."""
    sig = ('RB', 1, tuple(ell), len(ell))
    first = (c0,)
    left = []                 # frozen words: (kind, t, off)
    extra = []                # words pushed on the right, top last: (kind, t)
    bi = 0                    # next untouched block
    steps = 0
    nb = len(blocks)
    while True:
        if sig[0] in ('R', 'RB'):
            if first is not None:
                # the start: the head cell, then the first block, as one word
                k0, t0 = block_kind(*blocks[0]) if nb else block_kind(0, 0)
                kind, t = first + k0, t0
                first = None
                bi = 1
            elif extra:
                kind, t = extra.pop()
            else:
                kind, t = block_kind(*blocks[bi]) if bi < nb else block_kind(0, 0)
                bi += 1
            r = cross_right(sig, kind)
            if trace is not None:
                trace.append(('R', sig, kind, t, r[0]))
            if r[0] == 'halt':
                return None, steps, ('HALT', sig, kind, t)
            steps += ev(r[3], t)
            if r[0] == 'pass':
                if r[2]:
                    left.append(normalize(r[2], t) + (r[4],))
                sig = r[1]
            elif r[0] == 'turn':
                if r[2]:
                    extra.append(normalize(r[2], t))
                sig = r[1]
            else:
                ell2, toks, tt = r[1], r[2], t
                break
        else:
            if not left:
                raise Fail('left-moving with nothing on the left: %r' % (sig,))
            kind, t, off = left.pop()
            r = cross_left(sig, kind, off)
            if trace is not None:
                trace.append(('L', sig, kind, t, r[0]))
            if r[0] == 'halt':
                return None, steps, ('HALT', sig, kind, t)
            steps += ev(r[3], t)
            if r[0] == 'pass':
                if r[2]:
                    extra.append(normalize(r[2], t))
                sig = r[1]
            elif r[0] == 'turn':
                if r[2]:
                    left.append(normalize(r[2], t) + (r[4],))
                sig = r[1]
            else:
                ell2, toks, tt = r[1], r[2], t
                break
    if left:
        raise Fail('record with words left of the head')
    stream = subst(toks, tt)
    for kind, t in reversed(extra):
        stream += subst(kind, t)
    c, new = reparse(stream, blocks[bi:])
    return (ell2, c, new), steps, None


def reparse(stream, rest):
    """stream: cells / (word, n) items, followed by enc(rest) and then blank.  Returns (head cell, blocks)."""
    items = list(stream)
    mark = len(items)
    starts = {}
    for j, (D, x) in enumerate(rest):
        starts[len(items)] = j
        if D:
            items.append(((1, 0), D))
        items.append(x)
    pos = [0, 0]

    def peek(k):
        out = []
        i, off = pos
        while len(out) < k and i < len(items):
            z = items[i]
            if isinstance(z, int):
                out.append(z); i += 1; off = 0
            else:
                w, n = z
                L = len(w) * n
                while off < L and len(out) < k:
                    out.append(w[off % len(w)]); off += 1
                if off >= L:
                    i += 1; off = 0
        while len(out) < k:
            out.append(0)
        return out

    def adv(k):
        i, off = pos
        while k > 0 and i < len(items):
            z = items[i]
            if isinstance(z, int):
                i += 1; off = 0; k -= 1
            else:
                w, n = z
                L = len(w) * n
                s = min(k, L - off)
                off += s; k -= s
                if off >= L:
                    i += 1; off = 0
        pos[0], pos[1] = i, off

    def bulk_pairs():
        i, off = pos
        if i >= len(items) or isinstance(items[i], int):
            return 0
        w, n = items[i]
        if len(w) % 2 or any(w[j] == w[(j + 1) % len(w)] for j in range(len(w))):
            return 0
        if w[off % len(w)] != 1:
            return 0
        L = len(w) * n
        return max(0, (L - off) // 2 - 1)

    c0 = peek(1)[0]
    adv(1)
    out = []
    while True:
        if pos[1] == 0 and pos[0] in starts:
            out += list(rest[starts[pos[0]]:])
            break
        if pos[0] >= len(items):
            break
        D = 0
        while True:
            b = bulk_pairs()
            if b:
                D += b; adv(2 * b); continue
            if pos[0] < len(items) and peek(2) == [1, 0]:
                D += 1; adv(2); continue
            break
        x = peek(1)[0]
        adv(1)
        out.append((D, x))
    while out and out[-1] == (0, 0):
        out.pop()
    return c0, out

