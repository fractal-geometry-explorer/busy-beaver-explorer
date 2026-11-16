"""A transcription of the macro machine of lean/Sweep.lean (1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA).

A state is ('rt', out): the turn configuration RT out (D on the second cell of the last pair 11, the pairs `out`
on its left, nearest first, True = 11, False = 01, blank tape on the right), or ('raw', (l, r, st)): a configuration
on lists (left nearest first, head on r[0]), as FCfg in tools/lean/TM/Fin.lean.

mstep(state) -> ('go', n, state') | ('halt', n)."""

M = "1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA"
K = 1_000_000          # the raw part runs at most K steps per macro step (RAWK in Sweep.lean)


def table(m=M):
    T = {}
    for i, g in enumerate(m.split('_')):
        for r in range(2):
            t = g[3 * r:3 * r + 3]
            T[(chr(65 + i), r)] = None if t[2] == '-' else (t[0] == '1', t[1], t[2])
    return T


TT = table()


def cells(q):
    out = []
    for b in q:
        out += [b, True]
    return out


def scan(out):
    """the left pass from RT out, after its first 2 steps: ('turn', n, cs, q) | ('edgeD', n, m) | ('edgeF', n, m) |
    ('halt', n); m and q in reading order (left to right)."""
    l = out
    i = 0
    rm = [False]          # passed pairs, nearest first (reversed reading order)
    n = 0
    free = True
    while True:
        if i == len(l):
            return ('edgeF', n, rm[::-1]) if free else ('edgeD', n, rm[::-1])
        b = l[i]
        if free:
            rm.append(b)
            free = b
            i += 1
            n += 2
        elif b:
            rm.append(False)
            free = True
            i += 1
            n += 2
        else:
            if i + 1 == len(l):
                return ('halt', n + 2)
            c = l[i + 1]
            rm.append(True)
            rm.append(c)
            return ('turn', n + 3, l[i + 2:], rm[::-1])


def apass(cs, q):
    """the right pass from A on the first pair of q (cs on the left): every pair flips, then a new pair 11."""
    return [not a for a in reversed(q)] + list(cs), 2 * len(q) + 3


def fstep(c):
    l, r, s = c
    h = r[0] if r else False
    t = TT[(s, int(h))]
    if t is None:
        return None
    w, d, s2 = t
    if d == 'R':
        return ([w] + l, r[1:], s2)
    return (l[1:], [l[0] if l else False, w] + r[1:], s2)


def decode(l):
    """pairs of a left list after its first cell, or None"""
    out = []
    i = 0
    while i < len(l):
        if l[i]:
            if i + 1 < len(l):
                out.append(l[i + 1])
                i += 2
            else:
                out.append(False)
                i += 1
        else:
            return out if not any(l[i:]) else None
    return out


def as_rt(c):
    l, r, s = c
    if s != 'D' or not r or not r[0] or any(r[1:]) or not l or not l[0]:
        return None
    return decode(l[1:])


def mstep(state):
    kind, v = state
    if kind == 'rt':
        r = scan(v)
        if r[0] == 'turn':
            _, n, cs, q = r
            o, k = apass(cs, q)
            return ('go', n + 2 + k, ('rt', o))
        if r[0] == 'edgeD':
            _, n, m = r
            o, k = apass([], m)
            return ('go', n + 3 + k, ('rt', o))
        if r[0] == 'edgeF':
            _, n, m = r
            return ('go', n + 4, ('raw', ([], [False] + cells(m), 'A')))
        return ('halt', r[1] + 2)
    return raw_run(v)


def raw_run(c):
    """rawRun RAWK 0 c of Sweep.lean: fstep and as_rt after every step, on two stacks (the same lists, reversed)
    so that a step costs O(1); as_rt is tried only when its cheap conditions hold (state D, a 1 under the head,
    no other 1 on the right, a 1 on the left)."""
    l, r, s = c
    L = list(reversed(l))            # nearest cell last
    R = list(reversed(r))            # head cell last
    ones = sum(R)
    for i in range(1, K + 1):
        h = R[-1] if R else False
        t = TT[(s, int(h))]
        if t is None:
            return ('halt', i - 1)
        w, d, s = t
        if R:
            R.pop()
            ones -= h
        if d == 'R':
            L.append(w)
        else:
            x = L.pop() if L else False
            R.append(w)
            R.append(x)
            ones += w + x
        if s == 'D' and ones == 1 and R and R[-1] and L and L[-1]:
            o = decode(L[-2::-1])
            if o is not None:
                return ('go', i, ('rt', o))
    return ('go', K, ('raw', (L[::-1], R[::-1], s)))


def word(out):
    """the word of RT out, left to right, with the last pair: 1 = 11, 0 = 01."""
    return [int(b) for b in reversed(out)] + [1]
