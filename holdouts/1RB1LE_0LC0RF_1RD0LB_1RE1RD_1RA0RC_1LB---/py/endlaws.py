"""The round trip of the right-end layer as a recursion on the tail (README.md, "The round trip as a recursion").

usage (from the repository root):
  python3 holdouts/1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---/py/endlaws.py check [N] [I]   # the laws against G
  python3 holdouts/1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---/py/endlaws.py bfs [N] [I]     # every parity input, fast
  python3 holdouts/1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---/py/endlaws.py page            # explainer section "laws"

`FastModel` is `endlayer.Model` with the round trip run in C (c/roundtrip.c, built with cc into a temporary
directory and loaded with ctypes); it gives the same G.

The laws.  Write a tail as p y, where p is the front pattern (one token in a first slot, or an odd group followed
by one token, the second slot) and y is the rest.  Then G(p y) is one of
  freeze    h . y[j:]           the sweep turns back at p, y is not touched beyond its first j tokens
  continue  h . G(y)            the sweep goes on into y as if p were bulk
  double    h . G(G(y))[1:]     the part right of p gets two round trips in one visit
where the head h is a short word whose group sizes are affine in those of p and of the first token of y, G(y)
or G(G(y)).  `law(p, y)` returns the prediction, built from G of the rest; `check` compares it with G itself.
Not covered: an even group touching the next one (`2j_0`, the law depends on the next two or three tokens) and a
short gap in a second slot followed by a 1.
"""
import collections
import ctypes
import functools
import os
import pickle
import random
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from endlayer import END, MACHINES, MIRROR, SLOTS, Model, fmt, regular, split, table, tok2cells, toks  # noqa: E402

_LIB = None


def lib():
    global _LIB
    if _LIB is None:
        d = tempfile.mkdtemp()
        so = os.path.join(d, 'roundtrip.so')
        subprocess.run(['cc', '-O2', '-shared', '-fPIC', '-o', so, os.path.join(HERE, '..', 'c', 'roundtrip.c')],
                       check=True)
        _LIB = ctypes.CDLL(so)
        _LIB.roundtrip.restype = ctypes.c_int
        _LIB.roundtrip.argtypes = [ctypes.POINTER(ctypes.c_int), ctypes.c_char_p, ctypes.c_int, ctypes.c_int,
                                   ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_long]
    return _LIB


class FastModel(Model):
    NPRE = 8

    def __init__(self, machine):
        self.machine = machine
        self.T = table(machine, machine in MIRROR)
        arr = []
        for s in range(6):
            for r in range(2):
                t = self.T[(s, r)]
                arr += [-1, 0, 0] if t is None else list(t)
        self.CT = (ctypes.c_int * len(arr))(*arr)
        self.a = ord(SLOTS[machine][0]) - 65
        self.pre = [(1, 3)] * (2 * self.NPRE)
        self.ref = self._run(((2, END),))[1]

    def _run(self, tail, maxsteps=None):
        pc = tok2cells(self.pre)
        cells = pc + tok2cells(tail)
        n, base = len(cells) + 2000, 20
        buf = bytearray(n)
        for i, c in enumerate(cells):
            buf[i + base] = c == '1'
        cb = ctypes.create_string_buffer(bytes(buf), n)
        off = base + len(pc)
        r = lib().roundtrip(self.CT, cb, n, base, self.a, off, base, maxsteps or 200 * len(cells) ** 2 + 100000)
        if r:
            return ['HALT', 'RUNAWAY', 'TIMEOUT'][r - 1], None
        tape = cb.raw
        return ''.join('1' if b else '0' for b in tape[off - 1:]), tape[base + 48:off - 1]

    @functools.lru_cache(maxsize=200000)
    def G(self, tail):
        s, left = self._run(tuple(tail))
        if left is None:
            return s
        if left != self.ref:
            return 'LOOKS-LEFT'
        t = toks(s)
        return t if t is not None else 'NOT-GROUPS'


# ---------------------------------------------------------------- the laws
def ones(k):
    return ((1, 3),) * k


def law(M, p, y):
    """(kind, prediction of G(p + y)) for a front pattern p, or None if p is not covered."""
    r = _law(M, p, y)
    if r and r[0] == 'freeze' and len(y) == 1 and y[0][1] == END:
        # y is only the last group, and the sweep turns back on it: the last token written ends the tape
        w = r[1]
        r = (r[0], w[:-1] + ((w[-1][0], END),))
    return r


def sh(s, d):
    """A gap of s zeros made d longer (the end of the tape stays the end)."""
    return s if s == END else s + d


def _law(M, p, y):
    if len(p) == 1:                                   # a first slot
        (m, s), = p
        if not y:
            return None
        c, s0 = y[0]
        if m % 2 == 1 and s == 0:                     # odd group touching the next: freeze
            h = ones((m - 1) // 2) + (((1, sh(s0, 2)),) if c == 1 else ((1, 3), (c - 1, s0)))
            return 'freeze', h + y[1:]
        if m % 2 == 1 and s == 2:                     # short gap: double
            gg = M.G(M.G(y))
            a = gg[0]
            return 'double', ones((m - 1) // 2) + ((a[0] + 1, a[1]),) + gg[1:]
        if m % 2 == 1 and s == 5:                     # gap of five: continue
            return 'continue', ones((m - 1) // 2) + ((2, 3),) + M.G(y)
        if m % 2 == 0 and s == 3 and y[0] == (1, 0):  # even group, then a touching 1: halts (halt_even_touch)
            return 'halt', 'HALT'
        if m % 2 == 0 and s == 3:                     # even group: freeze, the counter is paid out
            h = ones(m // 2 - 1) + (((1, 3), (3, sh(s0, -1))) if c == 1 else ((1, 3), (3, 0), (c - 1, s0)))
            return 'freeze', h + y[1:]
        if m % 2 == 0 and s == 2:
            h = ones(m // 2) + (((1, sh(s0, 2)),) if c == 1 else ((1, 3), (c - 1, s0)))
            return 'freeze', h + y[1:]
        if m % 2 == 0 and s == 5:
            return 'freeze', ones(m // 2 - 1) + ((1, 3), (2, 2)) + y
        return None
    (a, sa), (m, s) = p                               # a second slot, after the odd group a
    if not (sa == 3 and a % 2 == 1) or not y:
        return None
    pre = ones((a - 1) // 2)
    c, s0 = y[0]
    if s == 3:
        return 'continue', pre + ((m + 2, 3),) + M.G(y)
    if s == 0:
        gg = M.G(M.G(y))
        return 'double', pre + ((gg[0][0] + m + 1, gg[0][1]),) + gg[1:]
    if s == 5:
        return 'freeze', pre + ((m + 2, 3),) + (((3, sh(s0, -1)),) if c == 1 else ((3, 0), (c - 1, s0))) + y[1:]
    if s == 2 and c >= 2:
        return 'freeze', pre + ((m + 2, 3),) + (((1, sh(s0, 2)),) if c == 2 else ((1, 3), (c - 2, s0))) + y[1:]
    return None


def samples(M, n, seed=1):
    """Front patterns p (sizes 1 to 12, gaps 000, 00, 5 zeros, none) and rests y taken from tails reached by `bfs`."""
    rnd = random.Random(seed)
    seen = bfs(M, 20000)
    tails = [t for t in seen if len(t) > 1]
    out = []
    for _ in range(n):
        t = rnd.choice(tails)
        y = t[rnd.randrange(len(t))]
        y = t[t.index(y):]
        m, s = rnd.randrange(1, 13), rnd.choice([3, 0, 2, 5])
        p = ((m, s),) if rnd.random() < .5 or (s == 3 and m % 2) else ((2 * rnd.randrange(6) + 1, 3), (m, s))
        out.append((p, y))
    return out


def check(M, n):
    stats = collections.Counter()
    bad = []
    for p, y in samples(M, n):
        try:
            r = law(M, p, y)
        except (TypeError, IndexError):          # G of the rest left the model (a halt or not in group form)
            stats['rest leaves the model'] += 1
            continue
        if r is None:
            stats['not covered'] += 1
            continue
        g = M.G(p + y)
        ok = g == r[1]
        stats[(r[0], 'ok' if ok else 'WRONG')] += 1
        if not ok and len(bad) < 5:
            bad.append((fmt(p), fmt(y), fmt(g), fmt(r[1])))
    return stats, bad


def bfs(M, limit, start=((2, END),)):
    """Breadth-first search of the tails reachable from `start`, the parity bit free at every round trip."""
    seen = {start: 0}
    q = collections.deque([start])
    while q and len(seen) < limit:
        t = q.popleft()
        U = M.G(t)
        if isinstance(U, str):
            raise SystemExit(f'{fmt(t)}: {U}')
        for y in (0, 1):
            nxt = split(U, y)
            if nxt not in seen:
                seen[nxt] = seen[t] + 1
                q.append(nxt)
    return seen


LAW_ROWS = [
    ('first', 'odd <i>m</i>, touching', 'freeze', '1<sup>(m&minus;1)/2</sup>, then 1 and c&minus;1 (c = 1: one 1 with a gap 2 longer)'),
    ('first', 'odd <i>m</i>, gap 00', 'double', '1<sup>(m&minus;1)/2</sup>, then a+1, where a is the first token of G(G(y))'),
    ('first', 'odd <i>m</i>, gap of 5', 'continue', '1<sup>(m&minus;1)/2</sup>, then 2'),
    ('first', 'even <i>m</i> = 2j', 'freeze', '1<sup>j&minus;1</sup>, then 1, 3 touching, c&minus;1 (c = 1: 1, 3 with gap 00); c a touching 1: halt'),
    ('first', 'even <i>m</i>, gap 00', 'freeze', '1<sup>j</sup>, then 1 and c&minus;1'),
    ('first', 'even <i>m</i>, gap of 5', 'freeze', '1<sup>j&minus;1</sup>, then 1 and 2 with gap 00; y untouched'),
    ('second', '<i>m</i>, gap 000', 'continue', 'm+2 (the pair rule)'),
    ('second', '<i>m</i>, touching', 'double', 'a+m+1, where a is the first token of G(G(y))'),
    ('second', '<i>m</i>, gap of 5', 'freeze', 'm+2, then 3 touching and c&minus;1 (c = 1: 3 with gap 00)'),
    ('second', '<i>m</i>, gap 00, c &ge; 2', 'freeze', 'm+2, then 1 and c&minus;2 (c = 2: one 1 with a gap 2 longer)'),
]

PAGE = """<p>The round trip of the tail is a recursion on the tail itself. Write the tail as <i>p y</i>: a front pattern
<i>p</i> (one group in a first slot, or an odd group and the group after it, the second slot) and the rest <i>y</i>.
Then G(<i>p y</i>) is one of three things:</p>
<ul>
<li><b>freeze</b>: <i>h</i> followed by <i>y</i> without its first token. The sweep turns back at <i>p</i>, so the rest
waits a round trip.</li>
<li><b>continue</b>: <i>h</i> followed by G(<i>y</i>). The sweep goes on as if <i>p</i> were bulk.</li>
<li><b>double</b>: <i>h</i> followed by G(G(<i>y</i>)) without its first token. The part right of <i>p</i> gets two
round trips in one visit.</li>
</ul>
<p>The head <i>h</i> is a short word whose group sizes are affine in the size <i>m</i> of <i>p</i> and the size
<i>c</i> of the first token of <i>y</i>. An odd group <i>a</i> in front of a second slot only adds
1<sup>(a&minus;1)/2</sup> in front. When <i>y</i> is only the last group, the last token written ends the tape.</p>
<div style="overflow-x:auto"><table class="tbl"><thead><tr><th>slot</th><th>p</th><th>kind</th><th>head h</th></tr></thead>
__ROWS__
</table></div>
<p>Two cases are not in the table: an even group touching the next group, whose law depends on the next two or three
tokens, and a gap 00 in a second slot followed by a single 1. On random tails these laws give exactly the
simulated G for all six machines (<code>py/endlaws.py check</code>: 30,000 front patterns per machine, none wrong,
about a quarter not covered).</p>
<p>The double case is why no small automaton describes the reachable tails. Each short gap doubles the speed of
everything right of it, and short gaps nest, so G is not a finite-state map. With the round trip in C
(<code>c/roundtrip.c</code>), the search over every parity input reaches 1,500,000 tails, 46 round trips deep,
without a halt.</p>"""


def page():
    import json
    path = os.path.join(HERE, '..', 'status.json')
    with open(path) as f:
        d = json.load(f)
    rows = '\n'.join(f'<tr><td>{a}</td><td>{b}</td><td>{c}</td><td>{e}</td></tr>' for a, b, c, e in LAW_ROWS)
    sec = {'id': 'laws', 'eyebrow': 'The right end', 'heading': 'The round trip as a recursion',
           'html': PAGE.replace('__ROWS__', rows)}
    ss = [s for s in d['explainer']['sections'] if s['id'] != 'laws']
    i = next(i for i, s in enumerate(ss) if s['id'] == 'end') + 1
    ss.insert(i, sec)
    d['explainer']['sections'] = ss
    with open(path, 'w') as f:
        f.write(json.dumps(d, indent=1, ensure_ascii=False) + '\n')


def main(argv):
    cmd = argv[1] if len(argv) > 1 else 'check'
    n = int(float(argv[2])) if len(argv) > 2 else 3000
    i = int(argv[3]) if len(argv) > 3 else 0
    M = FastModel(MACHINES[i])
    if cmd == 'check':
        stats, bad = check(M, n)
        for k, v in sorted(stats.items(), key=str):
            print(k, v)
        for b in bad:
            print('WRONG', *b, sep='\n  ')
    elif cmd == 'bfs':
        seen = bfs(M, n)
        print(MACHINES[i], len(seen), 'tails, depth', max(seen.values()), ', longest', max(map(len, seen)),
              'tokens, no halt')
    elif cmd == 'page':
        page()
    else:
        raise SystemExit(__doc__)


if __name__ == '__main__':
    main(sys.argv)
