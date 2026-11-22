"""Abstract trip of 1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB with inner trips as black boxes (see blackbox.py
for the minimal-counterexample argument), with the left side kept as runs instead of a window.

Left of the head: wall, BOTTOM (first NB runs), MIDDLE (any sequence of runs from the set S, possibly empty),
TOP (last <= N runs).  A run is (letter, a, star): length exactly a, or a + 3k (k >= 0) when star; a <= C.
S grows until it is closed.  The right side is a window of RW cells, unknown beyond.

With MODE=blank instead: the whole run from the blank tape, blank (not a wall) left of BOTTOM, every occurrence
of `0 0 0 1 1 A>` a black box by the trip lemma.

usage: [MODE=blank] python3 bbrun.py C N NB RW [K]"""
import os
import sys
from collections import deque

M = "1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB"
T = {}
for s, g in enumerate(M.split("_")):
    for y in (0, 1):
        x = g[3 * y:3 * y + 3]
        T[(s, y)] = None if x[0] == '-' else (int(x[0]), 1 if x[1] == 'R' else -1, "ABCDEF".index(x[2]))
EXITS = [(1, "111001"), (1, "011011"), (1, "111011"), (4, "111110"), (4, "111101"), (4, "111111")]
for e in os.environ.get("EXTRA", "").split():          # extra exits, as e.g. B011110
    EXITS.append(("ABCDEF".index(e[0]), e[1:]))
if os.environ.get("EXITFILE"):                           # exits as patterns over L cells, u = any
    EXITS = [("ABCDEF".index(l.split()[0]), l.split()[1]) for l in open(os.environ["EXITFILE"]) if l.strip()]
L = max(len(c) for _, c in EXITS)


def expand(c):
    c = c.ljust(L, "u")
    out = [""]
    for x in c:
        out = [o + y for o in out for y in (("0", "1") if x == "u" else (x,))]
    return out


CONC = {(s, w) for s, c in EXITS for w in expand(c)}


def covered(e):
    return all((e[0], w) in CONC for w in expand(e[1]))
C, N, NB, RW = map(int, sys.argv[1:5])
K = int(sys.argv[5]) if len(sys.argv) > 5 else 3
MAXS = 5_000_000
BLANK = os.environ.get("MODE") == "blank"


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


S = set()        # run types the middle may hold


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


absorbed = set()


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


def tr(right):
    right = right[:RW]
    return right.rstrip("u")


def step(x, halts, exits):
    st, bot, mid, top, right = x
    res = []
    empty_left = not top and not bot and not mid
    # black box?
    if BLANK and st == 0 and top and top[-1][0] == 1 and not bot and not mid and (
            len(top) == 1 or len(top) == 2 and top[0][0] == 0):
        res = []
        for k1, r1 in cases(top[-1], 3):
            if k1 == 'lt' and r1 == 2:
                for s2, cells in EXITS:
                    res.append((s2, (), 0, (), tr("0" + cells)))
            else:
                nr = (1, r1, False) if k1 == 'lt' else (grow(r1, 3) if r1 else (1, 3, False))
                res += normal((st, bot, mid, top[:-1] + (nr,), right), halts, exits)
        return res
    if st == 0 and len(top) >= 2 and top[-1][0] == 1 and top[-2][0] == 0:
        for k1, r1 in cases(top[-1], 3):
            if k1 == 'lt' and r1 == 2:
                for k0, r0 in cases(top[-2], 3):
                    if k0 == 'ge':
                        pre = top[:-2] + ((r0,) if r0 else ())
                        for b2, m2, t2, rt in [(bot, mid, pre, None)]:
                            for y in refill(st, b2, m2, t2, right):
                                _, b3, m3, t3, _ = y
                                if not t3 and not b3 and not m3:
                                    for e in EXITS:
                                        exits.add(e)
                                    continue
                                for s2, cells in EXITS:
                                    for c, b4, m4, t4 in pop(b3, m3, t3):
                                        res.append((s2, b4, m4, t4, tr(str(c) + cells)))
                    else:
                        res += normal((st, bot, mid, top[:-2] + ((0, r0, False), (1, 2, False)), right), halts, exits)
            else:
                nr = (1, r1, False) if k1 == 'lt' else (grow(r1, 3) if r1 else (1, 3, False))
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
                exits.add((s2, (str(w) + rest.replace("z", "0") + "u" * L)[:L]))
                continue
            for cc, b2, m2, t2 in pop(bot, mid, top):
                res += refill(s2, b2, m2, t2, tr(str(cc) + str(w) + rest))
    return res


start = (0, (), 0, ((0, 3, False), (1, 2, False)), "")
if BLANK:
    start = (0, (), 0, (), "z")
rnd = 0
reported = {}
while True:
    rnd += 1
    absorbed.clear()
    halts, exits = [], set()
    seen = {start}
    parent = {start: None}
    todo = deque([start])
    first = True
    while todo:
        x = todo.popleft()
        ne = len(exits)
        nx = normal(x, halts, exits) if first else step(x, halts, exits)
        if os.environ.get("TRACE") and len(exits) > ne:
            for e in exits:
                if not covered(e) and e not in reported:
                    reported[e] = x
        first = False
        for y in nx:
            if y not in seen:
                seen.add(y)
                parent[y] = x
                todo.append(y)
        if len(seen) > MAXS:
            break
    new = absorbed - S
    print(f"round {rnd}: states {len(seen)} |S| {len(S)} new {len(new)} halts {len(halts)} exits "
          f"{sorted(('ABCDEF'[s], c) for s, c in exits if not covered((s, c)))}", flush=True)
    if len(seen) > MAXS:
        print("too many states")
        break
    if not new:
        break
    S |= new
def show(x):
    st, bot, mid, top, right = x
    f = lambda r: ("0" if r[0] == 0 else "1") + "^" + str(r[1]) + ("+3k" if r[2] else "")
    return "ABCDEF"[st] + " | " + " ".join(map(f, bot)) + (" [S*] " if mid else " ") + " ".join(map(f, top)) + " > " + right
if os.environ.get("TRACE"):
    for e, x in list(reported.items())[:1]:
        print("path to exit", "ABCDEF"[e[0]], e[1])
        path = []
        while x is not None:
            path.append(x)
            x = parent[x]
        for x in reversed(path):
            print("  ", show(x))
for h in halts[:5]:
    print("halt", h)
print("S", sorted(S))
