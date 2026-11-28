"""Trip lemma search for 1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB as in bbrun.py, with BOTH sides as runs.

The left side is kept as in bbrun.py (wall, BOTTOM, MIDDLE from S, TOP).  The right side is a tuple of at most NR
runs followed by unknown cells; a run is (letter, a, star) as on the left, so long blocks written to the right
keep their length mod 3 instead of falling out of a window.  Inner trips are black boxes with the exits EXITS
(or, with EXITFILE, the patterns listed there); the tape right of an inner exit's six cells is unknown.

usage: python3 bbrr.py C N NB NR"""
import os
import sys
from collections import deque

M = "1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB"
T = {}
for s_, g in enumerate(M.split("_")):
    for y in (0, 1):
        x = g[3 * y:3 * y + 3]
        T[(s_, y)] = None if x[0] == '-' else (int(x[0]), 1 if x[1] == 'R' else -1, "ABCDEF".index(x[2]))
EXITS = [(1, "111001"), (1, "011011"), (1, "111011"), (4, "111110"), (4, "111101"), (4, "111111")]
for e in os.environ.get("EXTRA", "").split():
    EXITS.append(("ABCDEF".index(e[0]), e[1:]))
if os.environ.get("EXITFILE"):            # lines "STATE cells", cells over 0 1 u (u = any)
    EXITS = [("ABCDEF".index(l.split()[0]), l.split()[1]) for l in open(os.environ["EXITFILE"]) if l.strip()]
L = max(len(c) for _, c in EXITS)


def expand(c):
    out = [""]
    for x in c:
        out = [o + y for o in out for y in (("0", "1") if x == "u" else (x,))]
    return out


CONC = {(s_, w) for s_, c in EXITS for w in expand(c.ljust(L, "u"))}
BOX = sorted({(s_, w) for s_, c in EXITS for w in expand(c.rstrip("u"))})


def covered(e):
    return all((e[0], w) in CONC for w in expand(e[1]))
C, N, NB, NR = map(int, sys.argv[1:5])
K = 3
MAXS = int(float(os.environ.get("MAXS", "5e6")))
BLANK = False
S = set()
absorbed = set()


def mk(l, a, star):
    if a > C:
        k = (a - C + 2) // 3
        a -= 3 * k
        star = True
    return (l, a, star)


def cases(run, n):
    """[('lt', L)] exact lengths below n, [('ge', rest)] length >= n with n removed (rest None = empty)."""
    l, a, star = run
    out = []
    if not star:
        if a < n:
            return [('lt', a)]
        return [('ge', mk(l, a - n, False) if a > n else None)]
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


def grow(run, n):
    l, a, star = run
    return mk(l, a + n, star)




def refill(st, bot, mid, top, right):
    """All states with the same meaning whose TOP has >= K runs, or whose left is fully explicit."""
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
        top = top[:-1] + (grow(top[-1], 1),)
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
    """[(cell, bot, mid, top)]; top is nonempty here (or the left is blank)."""
    if not top:
        return [(0, bot, mid, top)]
    r = top[-1]
    out = []
    for kind, rest in cases(r, 1):
        out.append((r[0], bot, mid, top[:-1] + ((rest,) if rest else ())))
    return out




def rpush(right, w):
    """Put cell w in front of the right side."""
    if right and right[0][0] == w:
        right = (mk(w, right[0][1] + 1, right[0][2]),) + right[1:]
    else:
        right = ((w, 1, False),) + right
    if len(right) > NR:
        right = right[:NR]                     # forget the far runs: unknown from there on
    return right


def rpop(right):
    """[(cell or None for unknown, rest)]."""
    if not right:
        return [(None, ())]
    r = right[0]
    return [(r[0], ((rest,) if rest else ()) + right[1:]) for _, rest in cases(r, 1)]


def rcells(right, n):
    """[(first n cells as a string, 'u' unknown)]."""
    out = []
    stack = [("", right)]
    while stack:
        pre, r = stack.pop()
        if len(pre) == n:
            out.append(pre)
            continue
        for c, rest in rpop(r):
            stack.append((pre + ("u" if c is None else str(c)), rest))
    return out


def fromstr(cells):
    right = ()
    for ch in reversed(cells):
        right = rpush(right, int(ch))
    return right


def step(x, halts, exits, first):
    st, bot, mid, top, right = x
    if not first and st == 0 and top and top[-1][0] == 1:
        res = []
        for k1, r1 in cases(top[-1], 3):
            if k1 == 'lt' and r1 == 2:
                t1 = top[:-1]
                if t1 and t1[-1][0] == 0:
                    for k0, r0 in cases(t1[-1], 3):
                        if k0 == 'ge':
                            res += unbox(bot, mid, t1[:-1] + ((r0,) if r0 else ()), exits)
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


def unbox(bot, mid, pre, exits):
    res = []
    for y in refill(0, bot, mid, pre, ()):
        _, b3, m3, t3, _ = y
        if not t3 and not b3 and not m3:
            exits.update((s_, c.ljust(L, "u")) for s_, c in EXITS)
            continue
        for s2, cells in BOX:
            for c, b4, m4, t4 in pop(b3, m3, t3):
                res += refill(s2, b4, m4, t4, fromstr(str(c) + cells))
    return res


def normal(x, halts, exits):
    st, bot, mid, top, right = x
    res = []
    for c, rest in rpop(right):
        for b in ((0, 1) if c is None else (c,)):
            t = T[(st, b)]
            if t is None:
                halts.append(x)
                continue
            w, d, s2 = t
            if d == 1:
                b2, m2, t2 = push(bot, mid, top, w)
                res += refill(s2, b2, m2, t2, rest)
            else:
                r2 = rpush(rest, w)
                if not top and not bot and not mid:
                    for cells in rcells(r2, L):
                        exits.add((s2, cells))
                    continue
                for cc, b2, m2, t2 in pop(bot, mid, top):
                    res += refill(s2, b2, m2, t2, rpush(r2, cc))
    return res


def show(x):
    st, bot, mid, top, right = x
    f = lambda r: "01"[r[0]] + "^" + str(r[1]) + ("+3k" if r[2] else "")
    return ("ABCDEF"[st] + " | " + " ".join(map(f, bot)) + (" [S*] " if mid else " ") + " ".join(map(f, top))
            + " > " + " ".join(map(f, right)) + " ...")


start = (0, (), 0, ((0, 3, False), (1, 2, False)), ())
rnd = 0
while True:
    rnd += 1
    absorbed.clear()
    halts, exits = [], set()
    seen = {start}
    parent = {start: None}
    todo = deque([start])
    first = True
    badpath = None
    while todo:
        x = todo.popleft()
        e0 = len(exits)
        nx = step(x, halts, exits, first)
        first = False
        if badpath is None and len(exits) > e0 and any(not covered(e) for e in exits):
            badpath = x
        for y in nx:
            if y not in seen:
                seen.add(y)
                parent[y] = x
                todo.append(y)
        if len(seen) > MAXS:
            break
    new = absorbed - S
    bad = sorted(("ABCDEF"[s_], c) for s_, c in exits if not covered((s_, c)))
    print(f"round {rnd}: states {len(seen)} |S| {len(S)} new {len(new)} halts {len(halts)} extra exits {bad}",
          flush=True)
    if len(seen) > MAXS:
        print("too many states")
        break
    if not new:
        break
    S |= new
if os.environ.get("TRACE") and badpath is not None:
    path = []
    while badpath is not None:
        path.append(badpath)
        badpath = parent[badpath]
    for y in reversed(path):
        print("   ", show(y))
print("PROVED" if not halts and not bad and len(seen) <= MAXS else "not closed")
