"""Trip lemma for 1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB, and the whole run from it.

A *trip* is the run from `0 0 0 1 1 A> W` (W a finite word, then 0s) with the head kept right of the five region
cells; it ends when the head steps left of them (an *exit*).  The lemma, for a table H read from a file (lines
`prefix state cells`, as written by c/pexp.c):

    no trip halts, and a trip from W exits in a state s with cells c (the L cells from the region start)
    only if `W[:P] s c` is in H.

Proof by minimal counterexample.  In a shortest bad trip, each later configuration `0 0 0 1 1 A>` starts a
shorter trip, which therefore is good; so the bad trip is a run of the abstract system below in which each such
configuration is replaced by the exits H allows for the cells to its right that are known (or, at the region
itself, its exits are those of the outer trip).  The search below covers every run of that abstract system, for
every prefix p of W; if none halts and every exit of the trips from p is in H[p], the lemma holds.

Abstract configuration: state, the left side as runs (wall or blank, BOTTOM = first NB runs, MIDDLE = any
sequence of run types from a set S that grows until closed, TOP = last <= N runs), and the right side as a window
of RW cells ('u' unknown, 'z' zeros from here on).  A run is (letter, a, star): length a, or a + 3k when star.

usage: python3 bbtrip.py HFILE C N NB RW           trip lemma
       MODE=blank python3 bbtrip.py HFILE C N NB RW  the run from the blank tape, using the lemma"""
import os
import sys
from collections import deque, defaultdict
from itertools import product

M = "1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB"
T = {}
for s, g in enumerate(M.split("_")):
    for y in (0, 1):
        x = g[3 * y:3 * y + 3]
        T[(s, y)] = None if x[0] == '-' else (int(x[0]), 1 if x[1] == 'R' else -1, "ABCDEF".index(x[2]))
HFILE = sys.argv[1]
C, N, NB, RW = map(int, sys.argv[2:6])
K = 3
MAXS = int(float(os.environ.get("MAXS", "3e6")))
BLANK = os.environ.get("MODE") == "blank"

H = defaultdict(set)
for line in open(HFILE):
    if line.strip():
        p, s, c = line.split()
        H[p].add(("ABCDEF".index(s), c))
P = len(next(iter(H)))
L = len(next(iter(H[next(iter(H))]))[1])


def expand(c):
    return ["".join(t) for t in product(*[("0", "1") if x == "u" else (x,) for x in c])]


def prefix(right):
    out = []
    for i in range(P):
        if i < len(right):
            ch = right[i]
            if ch == "z":
                out.append("0" * (P - i))
                break
            out.append(ch)
        else:
            out.append("u")
    return "".join(out)


_bx = {}


def boxexits(right):
    p = prefix(right)
    if p not in _bx:
        _bx[p] = sorted(set().union(*[H[q] for q in expand(p)]))
    return _bx[p]


def mk(l, a, star):
    if a > C:
        k = (a - C + 2) // 3
        a -= 3 * k
        star = True
    return (l, a, star)


def cases(run, n):
    """[('lt', L)] exact lengths below n, [('ge', rest)] length >= n with n removed (rest None = empty)."""
    l, a, star = run
    if not star:
        if a < n:
            return [('lt', a)]
        return [('ge', mk(l, a - n, False) if a > n else None)]
    out = []
    k = 0
    while a + 3 * k < n:
        out.append(('lt', a + 3 * k))
        k += 1
    b = a + 3 * k - n
    if b >= 1:
        out.append(('ge', mk(l, b, True)))
    else:
        out.append(('ge', None))
        out.append(('ge', mk(l, 3, True)))
    return out


S = set()
absorbed = set()


def refill(st, bot, mid, top, right):
    out = []
    stack = [(bot, mid, top)]
    while stack:
        bot, mid, top = stack.pop()
        if len(top) >= K or (not mid and not bot):
            out.append((st, bot, mid, top, right))
            continue
        if mid:
            for r in S:
                if not top or r[0] != top[0][0]:
                    stack.append((bot, 1, (r,) + top))
            if bot and (not top or bot[-1][0] != top[0][0]):
                stack.append((bot[:-1], 0, (bot[-1],) + top))
            if not bot:
                stack.append(((), 0, top))
        else:
            stack.append((bot[:-1], 0, (bot[-1],) + top))
    return out


def push(bot, mid, top, w):
    if BLANK and w == 0 and not top and not bot and not mid:
        return bot, mid, top
    if top and top[-1][0] == w:
        top = top[:-1] + (mk(w, top[-1][1] + 1, top[-1][2]),)
    else:
        top = top + ((w, 1, False),)
    while len(top) > N:
        r, top = top[0], top[1:]
        if not mid and len(bot) < NB:
            bot = bot + (r,)
        else:
            absorbed.add(r)
            mid = 1
    return bot, mid, top


def pop(bot, mid, top):
    if not top:                      # blank left
        return [(0, bot, mid, top)]
    r = top[-1]
    return [(r[0], bot, mid, top[:-1] + ((rest,) if rest else ())) for _, rest in cases(r, 1)]


def tr(right):
    return right[:RW].rstrip("u")


def unbox(bot, mid, top, right, halts, exits):
    """Configuration A with the left ending in 0 0 0 1 1 (top already checked): its successors."""
    res = []
    for y in refill(0, bot, mid, top, right):
        _, b3, m3, t3, _ = y
        if not t3 and not b3 and not m3 and not BLANK:
            exits.update(boxexits(right))       # the rest of the outer trip is a trip from here
            continue
        for s2, cells in boxexits(right):
            for c, b4, m4, t4 in pop(b3, m3, t3):
                res += refill(s2, b4, m4, t4, tr(str(c) + cells))
    return res


def step(x, halts, exits):
    st, bot, mid, top, right = x
    if st == 0 and top and top[-1][0] == 1:
        res = []
        for k1, r1 in cases(top[-1], 3):
            if k1 == 'lt' and r1 == 2:
                t1 = top[:-1]
                if BLANK and not bot and not mid and (not t1 or len(t1) == 1 and t1[0][0] == 0):
                    res += unbox((), 0, (), right, halts, exits)
                elif t1 and t1[-1][0] == 0:
                    for k0, r0 in cases(t1[-1], 3):
                        if k0 == 'ge':
                            res += unbox(bot, mid, t1[:-1] + ((r0,) if r0 else ()), right, halts, exits)
                        else:
                            res += normal((st, bot, mid, t1[:-1] + ((0, r0, False), (1, 2, False)), right),
                                          halts, exits)
                else:
                    res += normal((st, bot, mid, t1 + ((1, 2, False),), right), halts, exits)
            else:
                nr = (1, r1, False) if k1 == 'lt' else (mk(1, r1[1] + 3, r1[2]) if r1 else (1, 3, False))
                res += normal((st, bot, mid, top[:-1] + (nr,), right), halts, exits)
        return res
    return normal(x, halts, exits)


def normal(x, halts, exits):
    st, bot, mid, top, right = x
    res = []
    c = right[0] if right else "u"
    if c == "z":
        c, right = "0", "zz"
    for b in ((0, 1) if c == "u" else (int(c),)):
        t = T[(st, b)]
        if t is None:
            halts.append(x)
            continue
        w, d, s2 = t
        rest = right[1:]
        if d == 1:
            b2, m2, t2 = push(bot, mid, top, w)
            res += refill(s2, b2, m2, t2, tr(rest))
        else:
            if not top and not bot and not mid and not BLANK:
                exits.add((s2, (str(w) + rest.replace("z", "0" * L) + "u" * L)[:L]))
                continue
            for cc, b2, m2, t2 in pop(bot, mid, top):
                res += refill(s2, b2, m2, t2, tr(str(cc) + str(w) + rest))
    return res


def show(x):
    st, bot, mid, top, right = x
    f = lambda r: "01"[r[0]] + "^" + str(r[1]) + ("+3k" if r[2] else "")
    return "ABCDEF"[st] + " | " + " ".join(map(f, bot)) + (" [S*] " if mid else " ") + " ".join(map(f, top)) + " > " + right


def explore(start, trace=None):
    halts, exits = [], set()
    seen = {start}
    parent = {start: None}
    todo = deque([start])
    first = True
    while todo:
        x = todo.popleft()
        ex0 = set(exits)
        nx = normal(x, halts, exits) if first else step(x, halts, exits)
        first = False
        if trace is not None:
            for e in exits - ex0:
                if any((e[0], w) not in H[trace] for w in expand(e[1])):
                    print("path to", "ABCDEF"[e[0]], e[1])
                    path = []
                    while x is not None:
                        path.append(x)
                        x = parent[x]
                    for y in reversed(path):
                        print("   ", show(y))
                    return None
        for y in nx:
            if y not in seen:
                seen.add(y)
                parent[y] = x
                todo.append(y)
        if len(seen) > MAXS:
            return None
    return len(seen), halts, exits


if BLANK:
    starts = [("blank", (0, (), 0, (), "z"))]
else:
    starts = [(p, (0, (), 0, ((0, 3, False), (1, 2, False)), p)) for p in sorted(H)]
    missing = [p for p in map("".join, product("01", repeat=P)) if p not in H]
    if missing:
        print("prefixes without exits in H:", missing)
rnd = 0
while True:
    rnd += 1
    absorbed.clear()
    _bx.clear()
    total, bad, grow_h = 0, [], 0
    for p, st in starts:
        r = explore(st, p if os.environ.get("TRACEP") == p else None)
        if r is None:
            print("too many states from", p)
            sys.exit(1)
        n, halts, exits = r
        total += n
        if BLANK:
            unc = sorted(exits)
        else:
            unc = [e for e in exits if any((e[0], w) not in H[p] for w in expand(e[1]))]
        if halts or unc:
            bad.append((p, halts[:3], sorted(unc)[:6]))
        if os.environ.get("GROW") and not halts:
            for e in unc:                  # widen the lemma by the exits found (a fixpoint, finite)
                for w in expand(e[1]):
                    if (e[0], w) not in H[p]:
                        H[p].add((e[0], w))
                        grow_h += 1
    new = absorbed - S
    print(f"round {rnd}: states {total} |S| {len(S)} new {len(new)} starts with problems {len(bad)}"
          f" table +{grow_h} (size {sum(map(len, H.values()))})", flush=True)
    if not new and not grow_h:
        break
    S |= new
if os.environ.get("HOUT"):
    with open(os.environ["HOUT"], "w") as f:
        for p in sorted(H):
            for s_, c in sorted(H[p]):
                f.write(f"{p} {'ABCDEF'[s_]} {c}\n")
for b in bad[:10]:
    print("  ", b)
print("S", sorted(S))
print("PROVED" if not bad else "not closed")
