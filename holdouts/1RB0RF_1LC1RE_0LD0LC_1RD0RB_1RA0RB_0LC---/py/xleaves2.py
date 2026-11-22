"""Symbolic case discovery for the irregular Q-steps of 1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RA---, which needs more
than `xleaves.py` gives: the collisions may read the end of the word, and a second misaligned gap may be pending
behind the one that collides.

As in `xleaves.py` the machine is run symbolically (`bbtools.symtm`) from each head until the next Q configuration,
splitting a count that may be 0 and expanding a context the head reaches.  The contexts here:

* `L` (the word in front of a collision, left of the head): its last block is odd and more word lies behind it
  (`L' 0 (11)^n 1`), or the word is a single even block on blank tape (`0^inf (11)^(n+1)`);
* the gaps: the aligned shapes of `xleaves.py` (a run of 2s, a run of 5s, a gap `3q+8`, blank tape) and, where a
  second misaligned gap is allowed, a gap `3q` or `3q+1`; after the second one only aligned shapes.

Heads (`t = 2s + p` gaps of 2, the colliding gap g in {0, 1}, then `u` gaps of 2):

* `coll p g`: `L 0 1 1 A> 0 1 (001001)^s [0 0 1] g (001)^u R`, where R is not a gap 2 and not a gap 0;
* `collz p g r`: the same with a second gap 0 behind the u gaps of 2, `u = 2v + r` written as `(001001)^v [001]`
  (with u as one count the case split does not end: the step depends on the parity of u);
* `anu`, `inner` as in `xleaves.py` (all gaps aligned).
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "../../../tools/py"))
from bbtools.symtm import Config, Rep, Lin, Ctx, Blank, tokens  # noqa: E402
from bbtools.machine import Machine  # noqa: E402
from xleaves import explore, parse_q, runs, segs_of, PErr, PSplit, subst_cfg  # noqa: E402


def expand2(name, fresh):
    i = next(fresh)
    if name.startswith('L'):
        return [tokens(f"L{i} 0 (11)^n{i} 1"), tokens(f"0^inf (11)^n{i}+1")]
    if not name.startswith('R'):
        return None
    kind = name.split('_')[0]
    x = kind.endswith('x')
    base = kind[:-1] if x else kind
    sx = 'x' if x else ''
    opts = []
    if base not in ('R', 'R2'):
        opts.append(tokens(f"(001)^m{i}+1 R2{sx}_{i}"))
    if base != 'R5':
        opts.append(tokens(f"(000001)^k{i}+1 R5{sx}_{i}"))
    opts.append(tokens(f"0 0 0 0 0 0 0 0 (000)^q{i} 1 Ra{sx}_{i}"))
    opts.append(tokens("0^inf"))
    if not x:
        if base == 'R':     # right behind the u gaps of 2: a gap 0 is the collz head
            opts.append(tokens(f"0 0 0 (000)^q{i} 1 Rax_{i}"))
        else:
            opts.append(tokens(f"(000)^q{i} 1 Rax_{i}"))
        opts.append(tokens(f"(000)^q{i} 0 1 Rax_{i}"))
    return opts


def heads2():
    for p, T in ((0, "(001001)^s"), (1, "(001001)^s 0 0 1")):
        for g, gs in ((0, "1"), (1, "0 1")):
            yield ('coll', p, g), f"L 0 1 1 A> 0 1 {T} {gs} (001)^u R"
            for r, rs in ((0, ""), (1, "0 0 1 ")):
                yield ('collz', p, g, r), f"L 0 1 1 A> 0 1 {T} {gs} (001001)^v {rs}1 Rax"
    yield ('anu',), "0^inf (11)^c+1 0 1 0 1 1 1 B> 0 Rax"
    yield ('inner',), "L 1 0 1 1 (11)^c 0 1 1 1 (111)^a B> 0 Rax"


def segs_of2(items):
    """As `segs_of`, with the misaligned gaps `3q` ('m0', q) and `3q+1` ('m1', q) as runs of their own."""
    out, rest = [], []
    for it in items:
        if it[0] == 'v' and it[1] not in (Lin(2), Lin(5)):
            g = it[1]
            vs = sorted(g.vars())
            r = g.k % 3
            if r != 2 and all(c == 3 for c in g.c.values()) and len(vs) <= 1:
                out.append(('m1' if r == 1 else 'm0', Lin(g.k // 3, dict(g.c and {vs[0]: 1}))))
                continue
        out.append(segs_of([it])[0] if segs_of([it]) else None)
    out = [x for x in out if x is not None]
    res = []
    for x in out:
        if res and res[-1][0] == x[0] and x[0] in ('two', 'five'):
            res[-1] = (x[0], res[-1][1] + x[1])
        else:
            res.append(x)
    return res


def word_start(cfg):
    """The word in front of a collision start `... 0 1 1 A>`: (anchor, blocks near first) or None if untouched."""
    L = cfg.left
    if L[-3:] != [0, 1, 1]:
        raise PErr('zc left')
    body = L[1:-3]
    if not body:
        return None
    items, cur = runs(body, 0)
    if isinstance(L[0], Ctx):
        if not items or items[0] != ('v', Lin(0)):
            raise PErr(f'word start {body}')
        items = items[1:]
    blocks = [it[1] for it in items if it[0] == 'v'] + [cur]
    if any(it[0] != 'v' for it in items):
        raise PErr('grouped word start')
    return L[0], list(reversed(blocks))


def peel(c):
    """Head cell inside a repeat of count >= 1: write one copy out (so that `parse_q` sees the cell)."""
    R = list(c.right)
    if R and isinstance(R[0], Rep) and R[0].n.surely_ge(1):
        R = list(R[0].word) + [Rep(R[0].word, R[0].n - 1)] + R[1:]
    return Config(list(c.left), c.state, R, c.steps)


def leaves2(machine, maxdepth=24):
    m = Machine.parse(machine)
    out = []
    for hk, st in heads2():
        todo = explore(m, Config.parse(st), expand2, maxdepth=maxdepth)
        while todo:
            lf = todo.pop(0)
            if lf.kind != 'rule':
                out.append(dict(head=hk, kind=lf.kind, leaf=lf))
                continue
            try:
                s, e = parse_q(lf.start), parse_q(peel(lf.end))
                d = dict(head=hk, kind='rule', leaf=lf, start=s, end=e)
                if hk[0] in ('coll', 'collz'):
                    p = hk[1]
                    pre = 1 + p + 1
                    gi = s['gaps'][pre:]
                    if hk[0] == 'collz':
                        # the gaps of 2 behind g, then the gap 0: their number is 2v + r
                        T, k = Lin(0), 0
                        while not (gi[k][0] == 'v' and gi[k][1] == Lin(0)):
                            it = gi[k]
                            if it[0] == 'g' and all(str(b) == '2' for b in it[1]):
                                T = T + len(it[1]) * it[2]
                            elif it[0] == 'v' and it[1] == Lin(2):
                                T = T + 1
                            else:
                                raise PErr(f"collz gaps {gi}")
                            k += 1
                        v2 = T - hk[3]
                        d['v'] = Lin(v2.k // 2, {x: c // 2 for x, c in v2.c.items()})
                        if 2 * d['v'] + hk[3] != T:
                            raise PErr(f"collz count {T}")
                        gi = gi[k + 1:]
                    d['segs'] = segs_of2(gi)
                    d['word'] = word_start(lf.start)
                elif hk[0] == 'anu':
                    d['segs'] = segs_of2(s['gaps'])
                    d['c'] = s['items'][0]
                else:
                    d['segs'] = []
            except PSplit as x:
                v = sorted(x.args[0].vars())[0]
                todo = (explore(m, subst_cfg(lf.start, v, Lin(0)), expand2, maxdepth=maxdepth) +
                        explore(m, subst_cfg(lf.start, v, Lin(v) + 1), expand2, maxdepth=maxdepth) + todo)
                continue
            out.append(d)
    return out


if __name__ == "__main__":
    import collections
    cnt = collections.Counter()
    for d in leaves2(sys.argv[1]):
        w = d.get('word')
        cnt[(d['head'], d['kind'], 'word' if w else '-')] += 1
        if d['kind'] != 'rule' or '-v' in sys.argv:
            print(d['head'], d['leaf'])
            if d['kind'] == 'rule':
                print('    segs', d['segs'], 'v', d.get('v'), d.get('ones'), 'word', w and (w[0], [str(b) for b in w[1]]))
    for k, v in sorted(cnt.items(), key=str):
        print(v, k)
