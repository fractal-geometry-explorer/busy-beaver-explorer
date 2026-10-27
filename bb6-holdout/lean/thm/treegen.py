"""Shared by the gen_*.py scripts: a serialized split tree (preorder tokens `N<i>`, `S<i>,<j>,<s>`, `A<n>`, `L<n>`)
written as Lean terms, and its check cut into subtrees.  One `decide +kernel` evaluation of a whole tree's check keeps
every intermediate term in the kernel's caches (it runs out of memory), so each subtree whose check runs at most
`budget` rounds gets its own theorem, and the theorem for the whole tree is assembled from them by the node and skew
lemmas (`Tree.okEnd_node`, `Tree.okEnd_skew`), which only unfold one step of the check.  An `adv n` above a cut is
moved down into the subtrees below it (each runs the n rounds itself).  The subtree theorems are spread over several
modules of about equal cost (`piece_modules`), which compile in parallel."""
import sys

sys.setrecursionlimit(1000000)


def parse(toks):
    pos = 0

    def go():
        nonlocal pos
        t = toks[pos]
        pos += 1
        if t[0] == 'L':
            return ('L', int(t[1:]))
        if t[0] == 'N':
            a = go()
            b = go()
            return ('N', int(t[1:]), a, b)
        if t[0] == 'S':
            i, j, s = t[1:].split(',')
            return ('S', int(i), int(j), int(s), go())
        if t[0] == 'A':
            return ('A', int(t[1:]), go())
        raise ValueError('bad token ' + t)

    t = go()
    assert pos == len(toks), 'trailing tokens'
    return t


def lint(n):
    return f'({n})' if n < 0 else str(n)


def term(t):
    if t[0] == 'L':
        return f'.leaf {t[1]}'
    if t[0] == 'N':
        return f'.node {t[1]} ({term(t[2])}) ({term(t[3])})'
    if t[0] == 'A':
        return f'.adv {t[1]} ({term(t[2])})'
    return f'.skew {t[1]} {t[2]} {lint(t[3])} ({term(t[4])})'


def cost(t):
    """Rounds the check runs in the subtree (a leaf or an advance also checks its start: one more)."""
    if t[0] == 'L':
        return t[1] + 1
    if t[0] == 'N':
        return cost(t[2]) + cost(t[3])
    if t[0] == 'A':
        return t[1] + 1 + cost(t[2])
    return cost(t[4])


def leaves(t):
    if t[0] == 'L':
        return 1
    if t[0] == 'N':
        return leaves(t[2]) + leaves(t[3])
    if t[0] == 'A':
        return leaves(t[2])
    return leaves(t[4])


class Kind:
    """How a check is stated: `check` (`okEnd`), its fixed arguments, the state constructors and the projections of a
    state onto the check's arguments."""

    def __init__(self, check, args, split, skew, proj, lemma):
        self.check, self.args, self.split, self.skew, self.proj, self.lemma = check, args, split, skew, proj, lemma

    def stmt(self, tree, st):
        return f'{tree}.{self.check} {self.args} false {self.proj(st)} = true'


def es_proj(es):
    return f'({es}).1.1 ({es}).1.2.1 ({es}).1.2.2 ({es}).2 0 none'


OKEND = lambda args: Kind('okEnd', args, 'esSplit', 'esSkew', es_proj, 'Tree.okEnd')


def cut(t, kind, root, prefix, budget):
    """Returns (skeleton term, proof term, pieces); a piece is (name, subtree term, state expression, cost)."""
    pieces = []

    def go(t, st, pend):
        # pend: rounds of advances above, moved down into this subtree
        if t[0] == 'A' and cost(t) + pend > budget:
            return go(t[2], st, pend + t[1])
        if cost(t) + pend <= budget or t[0] == 'L':
            name = f'{prefix}{len(pieces)}'
            if pend > 0:
                t = ('A', pend + t[1], t[2]) if t[0] == 'A' else ('A', pend, t)
            pieces.append((name, term(t), st, cost(t)))
            return name, f'{name}_ok'
        if t[0] == 'N':
            sa, pa = go(t[2], f'{kind.split} {wrap(st)} {t[1]} 0', pend)
            sb, pb = go(t[3], f'{kind.split} {wrap(st)} {t[1]} 1', pend)
            return f'(.node {t[1]} {sa} {sb})', f'({kind.lemma}_node (by decide) {pa} {pb})'
        sa, pa = go(t[4], f'{kind.skew} {wrap(st)} {t[1]} {t[2]} {lint(t[3])}', pend)
        return f'(.skew {t[1]} {t[2]} {lint(t[3])} {sa})', f'({kind.lemma}_skew (by decide) (by decide) (by decide) {pa})'

    def wrap(st):
        return st if ' ' not in st else f'({st})'

    skel, proof = go(t, root, 0)
    return skel, proof, pieces


def pieces_lean(kind, pieces):
    """A piece may carry its own kind as a fifth entry (trees of different checks in one module)."""
    out = []
    for p in pieces:
        name, tm, st = p[0], p[1], p[2]
        k = p[4] if len(p) > 4 else kind
        out.append(f'def {name} : Tree := {tm}\n')
        out.append(f'theorem {name}_ok : {k.stmt(name, st)} := by\n  decide +kernel\n')
    return '\n'.join(out)


def piece_modules(pieces, n):
    """Spread the pieces over n modules of about equal cost (largest first, each to the cheapest module so far);
    returns the lists of pieces, each in tree order."""
    bins = [[] for _ in range(n)]
    load = [0] * n
    for idx in sorted(range(len(pieces)), key=lambda i: -pieces[i][3]):
        b = min(range(n), key=lambda j: load[j])
        bins[b].append(idx)
        load[b] += pieces[idx][3]
    return [[pieces[i] for i in sorted(b)] for b in bins if b], load


def write_modules(outdir, base, header, kind, pieces, n):
    """Write the piece modules `{base}0.lean`, … (each `header`, then its pieces); returns their module names."""
    import os
    mods, load = piece_modules(pieces, n)
    names = []
    for i, ps in enumerate(mods):
        name = f'{base}{i}'
        open(os.path.join(outdir, name + '.lean'), 'w').write(header + '\n' + pieces_lean(kind, ps))
        names.append(name)
    return names, load
