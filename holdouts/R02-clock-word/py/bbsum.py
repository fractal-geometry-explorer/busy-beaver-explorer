"""Trip summaries for 1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB: an interprocedural (least-fixpoint) search.

A trip is the run from `0 0 0 1 1 A> W` until the head steps left of those five cells.  The search keeps, for
each abstract right side R (a tuple of at most NR runs, then unknown cells; a run is (letter, a, star): length a,
or a + 3k when star, a <= C), a summary SUM[R]: the abstract (state, right side from the region start) in which a
trip from a word in R can exit.  Inside a trip, every later `0 0 0 1 1 A>` is replaced by the summary of the
right side there; the left side is kept as in bbrun.py.  Summaries start empty and grow until nothing changes.

Soundness, by minimal counterexample: a shortest trip that halts or exits outside its summary contains only
shorter inner trips, which exit inside theirs; so it is a run of the abstract system, which has neither.

Then the run from the blank tape is explored the same way (blank left of everything).  If no exploration has a
halt, the machine does not halt.

usage: python3 bbsum.py C N NB NR"""
import os
import sys
from collections import deque, defaultdict

M = "1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB"
T = {}
for s_, g in enumerate(M.split("_")):
    for y in (0, 1):
        x = g[3 * y:3 * y + 3]
        T[(s_, y)] = None if x[0] == '-' else (int(x[0]), 1 if x[1] == 'R' else -1, "ABCDEF".index(x[2]))
C, N, NB, NR = map(int, sys.argv[1:5])
K = 3
MAXS = int(float(os.environ.get("MAXS", "3e6")))
BLANK = False
S = set()
absorbed = set()
SUM = {}
queried = set()


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


def run_le(r1, r2):
    """Every length of run r1 is a length of run r2 (same letter)."""
    if r1[0] != r2[0]:
        return False
    if not r2[2]:
        return r1 == r2
    return r1[1] >= r2[1] and (r1[1] - r2[1]) % 3 == 0


def right_le(a, b):
    """Every tape of right side a is a tape of right side b."""
    return len(a) >= len(b) and all(run_le(x, y) for x, y in zip(a, b))


def prune(entries):
    """Drop entries covered by another one."""
    out = []
    for e in sorted(entries, key=lambda e: len(e[1])):
        if not any(f[0] == e[0] and right_le(e[1], f[1]) for f in out):
            out.append(e)
    return set(out)


def summary(right):
    queried.add(right)
    return SUM.get(right, ())


def box(pre_bot, mid, pre, right, exits):
    """`L 0 0 0 1 1 A> right` with L = (pre_bot, mid, pre): successors after the inner trip."""
    res = []
    for _, b3, m3, t3, _ in refill(0, pre_bot, mid, pre, ()):
        empty = not t3 and not b3 and not m3
        for s2, ra in summary(right):
            if empty and not BLANK:
                exits.add((s2, ra))            # the rest of this trip is a trip from here
                continue
            for c, b4, m4, t4 in pop(b3, m3, t3):
                res += refill(s2, b4, m4, t4, rpush(ra, c))
    return res


def step(x, halts, exits, first):
    st, bot, mid, top, right = x
    if not first and st == 0 and top and top[-1][0] == 1:
        res = []
        for k1, r1 in cases(top[-1], 3):
            if k1 == 'lt' and r1 == 2:
                t1 = top[:-1]
                if BLANK and not bot and not mid and (not t1 or len(t1) == 1 and t1[0][0] == 0):
                    res += box((), 0, (), right, exits)
                elif t1 and t1[-1][0] == 0:
                    for k0, r0 in cases(t1[-1], 3):
                        if k0 == 'ge':
                            res += box(bot, mid, t1[:-1] + ((r0,) if r0 else ()), right, exits)
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
                if not top and not bot and not mid and not BLANK:
                    exits.add((s2, r2))
                    continue
                for cc, b2, m2, t2 in pop(bot, mid, top):
                    res += refill(s2, b2, m2, t2, rpush(r2, cc))
    return res


def show(x):
    st, bot, mid, top, right = x
    f = lambda r: "01"[r[0]] + "^" + str(r[1]) + ("+3k" if r[2] else "")
    return ("ABCDEF"[st] + " | " + " ".join(map(f, bot)) + (" [S*] " if mid else " ") + " ".join(map(f, top))
            + " > " + " ".join(map(f, right)) + " ...")


def explore(start):
    halts, exits = [], set()
    seen = {start}
    parent = {start: None}
    todo = deque([start])
    first = True
    while todo:
        x = todo.popleft()
        ne = set(exits)
        nx = step(x, halts, exits, first)
        first = False
        badx = [e for e in exits - ne if e[0] in (0, 3, 5)]
        if (halts or badx) and os.environ.get("TRACE"):
            print("from key", show((0, (), 0, (), start[4])), "bad exit" if badx else "halt", badx[:1])
            path = []
            while x is not None:
                path.append(x)
                x = parent[x]
            for y in reversed(path):
                print("   ", show(y))
            print("    halts")
            sys.exit(0)
        for y in nx:
            if y not in seen:
                seen.add(y)
                parent[y] = x
                todo.append(y)
        if len(seen) > MAXS:
            return None
    return len(seen), halts, exits


def run_key(k):
    global BLANK
    queried.clear()
    if k == "blank":
        BLANK = True
        r = explore((0, (), 0, (), ()))
        BLANK = False
    else:
        r = explore((0, (), 0, ((0, 3, False), (1, 2, False)), k))
    if r is None:
        print("too many states from", k, flush=True)
        sys.exit(1)
    return r, set(queried)


deps = defaultdict(set)
SUM[()] = set()
todo, inq = deque([()]), {()}
nexp, halted = 0, []
while True:
    absorbed.clear()
    while todo:
        k = todo.popleft()
        inq.discard(k)
        (n, halts, exits), q = run_key(k)
        nexp += 1
        if halts:
            halted.append(k)
            print("HALT in the trip from", show((0, (), 0, (), k)), flush=True)
        for k2 in q:
            deps[k2].add(k)
            if k2 not in SUM:
                SUM[k2] = set()
                todo.append(k2)
                inq.add(k2)
        newsum = prune(SUM[k] | exits)
        if newsum != SUM[k]:
            SUM[k] = newsum
            for k3 in deps[k]:
                if k3 not in inq:
                    todo.append(k3)
                    inq.add(k3)
        if nexp % 100 == 0:
            print(f"explorations {nexp} keys {len(SUM)} queue {len(todo)} summary entries "
                  f"{sum(map(len, SUM.values()))}", flush=True)
    new = absorbed - S
    print(f"pass: explorations {nexp} keys {len(SUM)} |S| {len(S)} new {len(new)}", flush=True)
    if not new:
        break
    S |= new
    todo, inq = deque(SUM), set(SUM)
(n, halts, exits), q = run_key("blank")
missing = [k for k in q if k not in SUM]
print("blank run: states", n, "halts", len(halts), "keys not summarised", len(missing))
ex = defaultdict(int)
for v in SUM.values():
    for s_, ra in v:
        ex["ABCDEF"[s_]] += 1
print("exit states in summaries:", dict(ex), " halting trips:", len(halted))
print("PROVED" if not halted and not halts and not missing else "not proved")
