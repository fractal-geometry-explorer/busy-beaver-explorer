"""Symbolic case discovery for the irregular Q-steps of the sister machines (family G12 word-and-counter).

Starting from a symbolic tape (`bbtools.symtm`), the machine is run until the next Q configuration (state B on a
0, a counter `0 1^(3a)` on the left).  Where the run needs to know more (a repeat count that may be 0, or a context
the head reaches), the case is split: a count into 0 and n+1, a context of counter gaps into the shapes an aligned
gap list can start with (a run of gaps 2, a run of gaps 5, a gap 3q+8, blank tape).  The leaves are rules that hold
for every value of their parameters and every tape in their remaining contexts.

Heads (all with a counter whose other gaps are aligned, `= 2 mod 3`):

* `coll p g`: the A phase of a collision, `L 0 1 1 A> 0 1 (001001)^s [0 0 1] g (001)^u R` (the `t = 2s + p` gaps of 2,
  the misaligned gap g in {0, 1}, then u gaps of 2 and the rest R);
* `anu`: the anomaly with a one-unit counter, word `[1, 2c+2]`, blank tape on the left;
* `inner`: the anomaly inside the word, a last block `2c+2` with more of the word behind it (`L 1`), counter `a+1`.

`leaves(machine)` returns the leaves with their parameters parsed into word/counter/gap terms for Lean
(`gen_xmap.py`).
"""
import itertools
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "../../../tools/py"))
from bbtools.symtm import (Config, run, Rep, Lin, Ctx, Blank, tokens, NeedSplit, TouchContext, Halted,  # noqa: E402
                           lin)
from bbtools.machine import Machine, STATES  # noqa: E402


class PErr(Exception):
    pass


class PSplit(PErr):
    """A repeat count that may be 0 where the parse needs at least one copy."""


# ---------------------------------------------------------------- exploration
def subst_lin(n, v, e):
    n = lin(n)
    a = n.c.get(v, 0)
    if not a:
        return n
    c = dict(n.c)
    del c[v]
    return Lin(n.k, c) + a * lin(e)


def subst_toks(toks, v, e):
    return [Rep(t.word, subst_lin(t.n, v, e)) if isinstance(t, Rep) else t for t in toks]


def subst_cfg(cfg, v, e):
    return Config(subst_toks(cfg.left, v, e), cfg.state, subst_toks(cfg.right, v, e), subst_lin(cfg.steps, v, e))


def replace_ctx(toks, name, new):
    out = []
    for t in toks:
        if isinstance(t, Ctx) and t.name == name:
            out.extend(new)
        else:
            out.append(t)
    return out


def left_cells_ones(left):
    tot, i = Lin(0), len(left) - 1
    while i >= 0:
        t = left[i]
        if t == 1:
            tot = tot + 1
        elif isinstance(t, Rep) and all(x == 1 for x in t.word):
            tot = tot + len(t.word) * t.n
        else:
            break
        i -= 1
    return tot, i


def is_sep(t):
    return t == 0 or (isinstance(t, Rep) and t.word[-1] == 0 and t.n.surely_ge(1))


def is_q_end(c):
    """A Q configuration: state B, head on a 0, then on the left a positive multiple of 3 ones and a 0."""
    if c.state != STATES.index('B') or c.steps.is_zero() or not c.right:
        return False
    h = c.right[0]
    if not (h == 0 or isinstance(h, Blank) or (isinstance(h, Rep) and h.word[0] == 0 and h.n.surely_ge(1))):
        return False
    n, i = left_cells_ones(c.left)
    if i < 0 or not is_sep(c.left[i]):
        return False
    if n.k % 3 or any(a % 3 for a in n.c.values()) or not n.surely_ge(3):
        return False
    return True


class Leaf:
    def __init__(s, kind, start, end=None, info=None):
        s.kind, s.start, s.end, s.info = kind, start, end, info

    def __repr__(s):
        return f"{s.kind}: {s.start}  ==>  {s.end if s.end else s.info}"


# Machines whose runs of gaps 2 are crossed two gaps at a time (the head rewrites a pair `0 0 1 0 0 1` as a block
# `1 1 1 1 1 0` and comes back): a run count is split by parity, and a run of even length `2v` is the repeat
# `(001001)^v`, so that one copy is crossed by a shift rule (the inductive crossing rule).
PAIRS = {"1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RC---"}
TWO, PAIR = (0, 0, 1), (0, 0, 1, 0, 0, 1)
_pairs = [False]


def pair_toks(toks):
    """`(001)^n` with every coefficient of n even: `0 0 1` (if the constant is odd) then `(001001)^(n/2)`."""
    out = []
    for t in toks:
        if isinstance(t, Rep) and t.word == TWO and t.n.c and all(a % 2 == 0 for a in t.n.c.values()):
            h = Lin(t.n.k // 2, {v: a // 2 for v, a in t.n.c.items()})
            out.extend(list(TWO) * (t.n.k % 2))
            out.append(Rep(PAIR, h))
        else:
            out.append(t)
    return out


def pair_cfg(cfg):
    return Config(pair_toks(cfg.left), cfg.state, pair_toks(cfg.right), cfg.steps)


def explore(m, start, expand, maxdepth=14, depth=0, fresh=None, max_moves=200000):
    if fresh is None:
        fresh = itertools.count()
    pairs = _pairs[0]
    if depth > maxdepth:
        return [Leaf('deep', start, info='depth')]
    try:
        fin = run(m, start.copy(), is_q_end, max_moves=max_moves, rotate=True)
        return [Leaf('rule', start, fin)]
    except NeedSplit as e:
        r = e.args[0]
        v = sorted(r.n.vars())[0]
        if pairs and r.word == TWO and r.n.c.get(v, 0) % 2 == 1:
            return (explore(m, pair_cfg(subst_cfg(start, v, 2 * Lin(v))), expand, maxdepth, depth + 1, fresh,
                            max_moves) +
                    explore(m, pair_cfg(subst_cfg(start, v, 2 * Lin(v) + 1)), expand, maxdepth, depth + 1, fresh,
                            max_moves))
        return (explore(m, subst_cfg(start, v, Lin(0)), expand, maxdepth, depth + 1, fresh, max_moves) +
                explore(m, subst_cfg(start, v, Lin(v) + 1), expand, maxdepth, depth + 1, fresh, max_moves))
    except TouchContext as e:
        x = e.args[0]
        name = x.name if isinstance(x, Ctx) else str(x)
        opts = expand(name, fresh)
        if opts is None:
            return [Leaf('touch', start, info=name)]
        out = []
        for toks in opts:
            st = Config(replace_ctx(start.left, name, toks), start.state, replace_ctx(start.right, name, toks),
                        start.steps)
            out += explore(m, st, expand, maxdepth, depth + 1, fresh, max_moves)
        return out
    except Halted as e:
        return [Leaf('halt', start, info=str(e))]
    except RuntimeError as e:
        return [Leaf('runaway', start, info=str(e)[:100])]


def expand(name, fresh):
    """Contexts of aligned gaps: R (after a run of 2s), R2 (after a run of 2s), R5 (after a run of 5s), Ra (any)."""
    if not name.startswith('R'):
        return None
    kind = name.split('_')[0]
    i = next(fresh)
    opts = []
    if kind not in ('R', 'R2'):
        opts.append(tokens(f"(001)^m{i}+1 R2_{i}"))
    if kind != 'R5':
        opts.append(tokens(f"(000001)^k{i}+1 R5_{i}"))
    opts.append(tokens(f"0 0 0 0 0 0 0 0 (000)^q{i} 1 Ra_{i}"))
    opts.append(tokens("0^inf"))
    return opts


def heads():
    for p, T in ((0, "(001001)^s"), (1, "(001001)^s 0 0 1")):
        for g, gs in ((0, "1"), (1, "0 1")):
            yield ('coll', p, g), f"L 0 1 1 A> 0 1 {T} {gs} (001)^u R"
    yield ('anu',), "0^inf (11)^c+1 0 1 0 1 1 1 B> 0 Ra"
    yield ('inner',), "L 1 0 1 1 (11)^c 0 1 1 1 (111)^a B> 0 Ra"


# ---------------------------------------------------------------- parsing tapes into blocks and gaps
def runs(toks, sep):
    """Cells left to right, split at single `sep` cells into runs of the other symbol: items ('v', Lin) or
    ('g', [Lin...], n) (a group of runs repeated n times), and the trailing run not closed by `sep`."""
    other = 1 - sep
    out, cur = [], Lin(0)
    for t in toks:
        if t == other:
            cur = cur + 1
        elif t == sep:
            out.append(('v', cur))
            cur = Lin(0)
        elif isinstance(t, Rep):
            w, n = t.word, t.n
            if sep not in w:
                cur = cur + sum(1 for x in w if x == other) * n
                continue
            parts, c = [], 0
            for x in w:
                if x == other:
                    c += 1
                else:
                    parts.append(c)
                    c = 0
            a, inner, last = parts[0], parts[1:], c
            if cur.is_zero() and last == 0:
                out.append(('g', [Lin(a)] + [Lin(x) for x in inner], n))
                continue
            if not n.surely_ge(1):
                raise PSplit(t.n)
            out.append(('v', cur + a))
            for x in inner:
                out.append(('v', Lin(x)))
            out.append(('g', [Lin(last + a)] + [Lin(x) for x in inner], n - 1))
            cur = Lin(last)
        else:
            raise PErr(f"token {t}")
    return [it for it in out if not (it[0] == 'g' and it[2].is_zero())], cur


def parse_q(c):
    """A Q configuration (or a zc one, state A): anchor, counter a, word items (far -> near; with a context anchor
    the first item is the number of ones added to the anchor's last block), gap items, tail."""
    L = c.left
    if not L or not isinstance(L[0], (Ctx, Blank)):
        raise PErr('left anchor')
    if c.state == STATES.index('B'):
        n, i = left_cells_ones(L)
        if n.k % 3 or any(a % 3 for a in n.c.values()):
            raise PErr('counter')
        a = Lin(n.k // 3, {v: x // 3 for v, x in n.c.items()})
        body = L[1:i] + [0] if L[i] == 0 else L[1:i + 1]
        R = list(c.right)
        if R and R[0] == 0:
            R = R[1:]
        elif not (R and isinstance(R[0], Blank)):
            raise PErr('head cell')
    else:   # zc L G: L 0 1 1 A> 0 1 gaps
        if L[-3:] != [0, 1, 1]:
            raise PErr('zc left')
        a, body = None, None
        R = list(c.right)
        if R[:2] != [0, 1]:
            raise PErr('zc right')
        R = R[2:]
    items = runs(body, 0)[0] if body is not None else None
    tail = None
    if R and isinstance(R[-1], (Ctx, Blank)):
        tail, R = R[-1], R[:-1]
    gitems, gcur = runs(R, 1)
    if not gcur.is_zero() and not isinstance(tail, Blank):
        raise PErr(f'partial gap before context {gcur}')
    return dict(anchor=L[0], a=a, items=items, gaps=gitems, tail=tail)


# ---------------------------------------------------------------- Lean terms
def ln(x):
    x = lin(x)
    s = x.lean()
    return s if (" " not in s) else f"({s})"


def word_expr(items, rest="[]"):
    """Items far -> near as a Lean list, near first, nested to the right (`x :: (...)`, `replicate .. ++ (...)`)."""
    e = rest
    for it in items:
        if it[0] == 'v':
            e = f"{ln(it[1])} :: ({e})" if e != "[]" else f"[{ln(it[1])}]"
        else:
            bs = it[1]
            if len(set(map(str, bs))) != 1:
                raise PErr(f"mixed group {it}")
            e = f"List.replicate ({(len(bs) * it[2]).lean()}) {ln(bs[0])} ++ ({e})"
    return e


def gap_expr(items, rest):
    """Gap items (near first) as a Lean list ending in `rest`."""
    e = rest
    for it in reversed(items):
        if it[0] == 'v':
            e = f"{ln(it[1])} :: {e}"
        else:
            bs = it[1]
            if len(set(map(str, bs))) != 1:
                raise PErr(f"mixed group {it}")
            e = f"List.replicate ({(len(bs) * it[2]).lean()}) {ln(bs[0])} ++ {e}"
    return e


def segs_of(items):
    """Gap items of a start (after any fixed prefix) as segments: ('two', n), ('five', n), ('big', q)."""
    out = []
    for it in items:
        if it[0] == 'g' and [str(b) for b in it[1]] == ['2']:
            out.append(('two', it[2]))
        elif it[0] == 'g' and [str(b) for b in it[1]] == ['2', '2']:
            out.append(('two', 2 * it[2]))
        elif it[0] == 'g' and [str(b) for b in it[1]] == ['5']:
            out.append(('five', it[2]))
        elif it[0] == 'v' and it[1] == Lin(5):
            out.append(('five', Lin(1)))
        elif it[0] == 'v' and it[1] == Lin(2):
            out.append(('two', Lin(1)))
        elif it[0] == 'v':
            g = it[1] - 8
            vs = sorted(g.vars())
            if g.k == 0 and len(vs) == 1 and g.c[vs[0]] == 3:
                out.append(('big', Lin(vs[0])))
            elif g.is_const() and g.k >= 0 and g.k % 3 == 0:
                out.append(('big', Lin(g.k // 3)))
            else:
                raise PErr(f"gap {it}")
        else:
            raise PErr(f"segment {it}")
    # a run that may be empty is split by the caller; an empty run is left out
    for kind, n in out:
        if kind in ('two', 'five') and not n.is_const() and n.k == 0:
            raise PSplit(n)
    out = [(kind, n) for kind, n in out if not (kind in ('two', 'five') and n.is_const() and n.k == 0)]
    # merge adjacent runs of the same kind
    res = []
    for s in out:
        if res and res[-1][0] == s[0] and s[0] in ('two', 'five'):
            res[-1] = (s[0], res[-1][1] + s[1])
        else:
            res.append(s)
    return res


def seg_pat(segs, tail):
    """A Lean pattern for a list of segments (`Sg`) ending in the context `S` or in []."""
    e = "S" if isinstance(tail, Ctx) else "[]"
    for kind, n in reversed(segs):
        e = f".{kind} {ln(n)} :: {e}"
    return e


def tail_expr(tail):
    return "flat S" if isinstance(tail, Ctx) else "[]"


def leaves(machine):
    m = Machine.parse(machine)
    _pairs[0] = machine in PAIRS
    out = []
    for hk, st in heads():
        todo = explore(m, Config.parse(st), expand)
        while todo:
            lf = todo.pop(0)
            if lf.kind != 'rule':
                out.append(dict(head=hk, kind=lf.kind, leaf=lf))
                continue
            try:
                s, e = parse_q(lf.start), parse_q(lf.end)
                d = dict(head=hk, kind='rule', leaf=lf, start=s, end=e)
                if hk[0] == 'coll':
                    p = hk[1]
                    pre = 1 + p + 1          # (001001)^s, [0 0 1], g
                    d['segs'] = segs_of(s['gaps'][pre:])
                elif hk[0] == 'anu':
                    d['segs'] = segs_of(s['gaps'])
                    d['c'] = s['items'][0]   # block (11)^(c+1): 2c+2
                else:
                    d['segs'] = []
            except PSplit as x:
                v = sorted(x.args[0].vars())[0]
                todo = (explore(m, subst_cfg(lf.start, v, Lin(0)), expand) +
                        explore(m, subst_cfg(lf.start, v, Lin(v) + 1), expand) + todo)
                continue
            if _pairs[0] and d['segs']:
                d = canon_names(d)
            out.append(d)
    return out


def canon_names(d):
    """Rename the variables of the gap runs to `x0, x1, ...` (by run), so that the leaves of the two parities of a
    run of 2s have the same names and can share one case of the decision function."""
    ren = {}
    for i, (kind, n) in enumerate(d['segs']):
        for v in n.vars():
            ren.setdefault(v, f"x{i}")
    if not ren:
        return d
    lf = d['leaf']
    tmp = {v: f"_t{j}" for j, v in enumerate(ren)}
    st, en = lf.start, lf.end
    for v, t in tmp.items():
        st, en = subst_cfg(st, v, Lin(t)), subst_cfg(en, v, Lin(t))
    for v, t in tmp.items():
        st, en = subst_cfg(st, t, Lin(ren[v])), subst_cfg(en, t, Lin(ren[v]))
    lf2 = Leaf(lf.kind, st, en, lf.info)
    s, e = parse_q(st), parse_q(en)
    d2 = dict(d, leaf=lf2, start=s, end=e)
    hk = d['head']
    if hk[0] == 'coll':
        d2['segs'] = segs_of(s['gaps'][1 + hk[1] + 1:])
    else:
        d2['segs'] = segs_of(s['gaps'])
        d2['c'] = s['items'][0]
    return d2


if __name__ == "__main__":
    import collections
    cnt = collections.Counter()
    for d in leaves(sys.argv[1]):
        cnt[(d['head'], d['kind'])] += 1
        if d['kind'] != 'rule':
            print(d['head'], d['leaf'])
            continue
        e = d['end']
        print(d['head'], seg_pat(d['segs'], d['start']['tail']), '|', d['start']['items'], '=>  a', e['a'], 'W',
              e['items'], 'G', gap_expr(e['gaps'], tail_expr(e['tail'])))
    for k, v in sorted(cnt.items(), key=str):
        print(v, k)
