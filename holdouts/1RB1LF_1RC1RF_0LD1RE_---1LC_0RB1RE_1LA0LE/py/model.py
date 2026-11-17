"""The right-end map of 1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE, as exact arithmetic.

At every visit of the right end in state B the tape is

    T(c, a, b) = 0^inf [1^2 0 (10)^c] 1^a 0 (10)^b B> 0^inf        (c = None: no bracket)

`step(c, a, b)` is the next visit (or "halt").  Between two visits the machine goes through the inner configurations
C(x, p, w): a pool 1^x, a middle block 1^p and a tail worth w rounds; `step` is that loop with its rounds jumped:

    round      (x, p, w) -> (x - 2, p + 4, w - 1)
    w = 0      visit T(x - 2, p/2 + 1)                               (pool not empty: the doubling step)
    x = 2      carry: (p + 4, 2, w - 2); if w is 0 or 1 instead: visit T(p + 3, 0) (odd!) or T(p + 4, 0)
    x = 3      an odd pool runs out: without a bracket the middle block stays behind as a bracket and the pool is 2;
               with a bracket the bracket is added to the middle block and the bracket is gone

For even a (the bracket is not touched), with u = b + 2 and v = a/2 + b + 3, this is a doubling map:

    2u < v     T(a - 2b - 2, 2b + 2):   u <- 2u,      v <- v + 1      (a visit)
    2u > v     carry, no visit:         u <- 2u - v,  v unchanged     (as if at T(2a + 2, b - a/2 - 1))
    2u = v     T(c, 2v - 3, 0): an odd pool

The only halting visits are T(None, 1, b).  An odd pool without bracket always starts as T(None, A, 0), and it
reaches 1 exactly when A = 2^(k+2) - 2k - 3 for some k (`halting_pool`): 1, 3, 9, 23, 53, 115, 241, 495, 1005, ...

    python3 py/model.py check          # step against direct simulation: a grid, the run from blank tape, the doubling map
    python3 py/model.py rules          # op (lean/Doubling.lean) and op_steps against direct simulation
    python3 py/model.py events 1e6     # the odd pools of the first 10^6 operations of the run
    ./rec MACHINE 3000000000 R B 10000000 | python3 py/model.py checkrec    # every visit of 3*10^9 steps (c/rec.c)
    python3 py/model.py dump 5000      # the first visits "c a b" (c = -1: none), same output as `c/fast dump 5000`
"""
import re
import sys

M = "1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE"
PAT = re.compile(r"(?:(11)0((?:10)*))?(1*)0((?:10)*)")
START = (None, 2, 0)        # reached at step 7 from blank tape


def norm(c, a, b):
    """T(c, 1, b) and T(None, 2, c + b + 1) are the same tape."""
    return (None, 2, c + b + 1) if c is not None and a == 1 else (c, a, b)


def step(c, a, b, count=None):
    """The visit after T(c, a, b) (a >= 2, or a = 1 without bracket: halt).  `count`: a list whose first entry is
    increased by the number of operations (passes of the loop)."""
    if c is None and a == 1:
        return "halt"
    assert a >= 2
    x, p, w = a, 2, b
    while True:
        if count:
            count[0] += 1
        if x % 2 == 0:
            k = (x - 2) // 2                      # rounds until the pool is 1^2
            if w <= k - 1:
                return norm(c, x - 2 * w - 2, p // 2 + 2 * w + 1)
            p += 4 * k; w -= k; x = 2
            if w == 0:
                return norm(c, p + 3, 0)          # odd pool
            if w == 1:
                return norm(c, p + 4, 0)
            x = p + 4; p = 2; w -= 2              # carry
        else:
            k = (x - 3) // 2                      # rounds until the pool is 1^3
            if w <= k:
                return norm(c, x - 2 * w - 2, p // 2 + 2 * w + 1)
            p += 4 * k; w -= k; x = 3
            if c is None:
                p += 4; w -= 1                    # one more round: the pool is 1
                if w >= 3:
                    c = p // 2 + 1; x = 2; p = 2; w -= 3      # the middle block becomes the bracket
                elif w == 2:
                    return norm(p // 2 + 1, 2, 0)
                elif w == 1:
                    x = 2; w = p // 2 + 1; p = 2              # as if at T(None, 2, p/2 + 1)
                else:
                    return norm(None, p + 5, 0)               # odd pool again
            else:
                p = 2 * c + p + 6; c = None; x = 2; w -= 1    # the bracket joins the middle block


def halting_pool(A):
    """Does T(None, A, 0) (A odd) lead to a halt?  The doubling steps give a = A - 2^(k+2) + 2k + 4, b = 2^(k+1) - 2."""
    k = 0
    while (1 << (k + 2)) - 2 * k - 3 < A:
        k += 1
    return (1 << (k + 2)) - 2 * k - 3 == A


def table():
    T = {}
    for i, g in enumerate(M.split("_")):
        for s in (0, 1):
            t = g[3 * s:3 * s + 3]
            T[(i, s)] = None if t[0] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
    return T


def word(c, a, b):
    return ("11" + "0" + "10" * c if c is not None else "") + "1" * a + "0" + "10" * b


def parse_t(tape, lo, pos):
    a = lo
    while a < pos and tape.get(a, 0) == 0:
        a += 1
    m = PAT.fullmatch("".join(str(tape.get(x, 0)) for x in range(a, pos)))
    if not m:
        return None
    return norm(len(m.group(2)) // 2 if m.group(1) else None, len(m.group(3)), len(m.group(4)) // 2)


def sim(c, a, b, limit=10 ** 7):
    """Direct simulation from T(c, a, b) to the next visit of the right end in state B."""
    T = table()
    w = word(c, a, b)
    tape = {i: int(ch) for i, ch in enumerate(w)}
    pos, st, lo, hi = len(w), 1, 0, len(w)
    for _ in range(limit):
        t = T[(st, tape.get(pos, 0))]
        if t is None:
            return "halt"
        tape[pos] = t[0]; pos += t[1]; st = t[2]
        lo = min(lo, pos)
        if pos > hi:
            hi = pos
            if st == 1:
                r = parse_t(tape, lo, pos)
                if r:
                    return r
    return "?"


def check():
    bad = n = 0
    for c in (None, 0, 1, 2, 3, 4, 7, 10):
        for a in range(1, 40):
            for b in range(0, 44):
                n += 1
                if sim(c, a, b) != step(*norm(c, a, b)):
                    bad += 1; print("grid: differs at", c, a, b)
    print(f"grid: {n} configurations, {bad} failures")
    # the run from blank tape
    T = table()
    tape, pos, st, lo, hi, cur, visits = {}, 0, 0, 0, 0, None, 0
    for k in range(3 * 10 ** 6):
        t = T[(st, tape.get(pos, 0))]
        tape[pos] = t[0]; pos += t[1]; st = t[2]
        lo = min(lo, pos)
        if pos > hi:
            hi = pos
            if st == 1 and k + 1 >= 7:
                r = parse_t(tape, lo, pos)
                if r is None:
                    bad += 1; print("run: not a T at step", k + 1); continue
                cur = step(*cur) if cur else START
                visits += 1
                if cur != r:
                    bad += 1; print("run: differs at step", k + 1, cur, r); cur = r
    print(f"run: {visits} visits in 3e6 steps, {'ok' if not bad else 'FAILED'}")
    # the doubling map on even pools
    nd = 0
    for a in range(2, 120, 2):
        for b in range(0, 120):
            u, v = b + 2, a // 2 + b + 3
            r = step(None, a, b)
            while 2 * u > v:
                u = 2 * u - v
            want = (None, 2 * v - 3, 0) if 2 * u == v else (None, 2 * (v + 1 - 3 - (2 * u - 2)), 2 * u - 2)
            nd += 1
            if r != want:
                bad += 1; print("doubling map differs at", a, b, r, want)
    print(f"doubling map: {nd} even configurations, {'ok' if not bad else 'FAILED'}")
    # halting pools
    for A in range(1, 400, 2):
        s, h = (None, A, 0), False
        while s != "halt" and s[0] is None and s[1] % 2 == 1:
            s = step(*s)
        if (s == "halt") != halting_pool(A):
            bad += 1; print("halting pool differs at", A)
    print("halting pools A < 400:", "ok" if not bad else "FAILED")
    return bad


def checkrec():
    """stdin: the output of c/rec.c (visits of the right end in state B, run-length coded)."""
    cur, n, st = None, 0, 0
    for line in sys.stdin:
        if not line[0].isdigit() or int(line.split()[0]) < 7:
            continue
        cells = []
        for t in line.split()[1:]:
            if t.startswith("B>"):
                break
            cells.append(t[0] * int(t[2:]) if "^" in t else t)
        m = PAT.fullmatch("".join(cells).lstrip("0"))
        st = int(line.split()[0])
        if not m:
            print("not a T at step", st); return 1
        r = norm(len(m.group(2)) // 2 if m.group(1) else None, len(m.group(3)), len(m.group(4)) // 2)
        cur = step(*cur) if cur else START
        if cur != r:
            print("differs at step", st, cur, r); return 1
        n += 1
    print(f"{n} visits agree; the last at step {st}: {cur}")
    return 0


def events(maxops):
    s, cnt, visits = START, [0], 0
    while cnt[0] < maxops:
        s = step(*s, count=cnt)
        if s == "halt":
            print("HALT at visit", visits); return
        visits += 1
        if s[1] % 2 == 1 and s[2] == 0:
            print(f"visit {visits} ops {cnt[0]}: T({'none' if s[0] is None else s[0]}, {s[1]}, 0)"
                  + ("   HALTING POOL" if s[0] is None and halting_pool(s[1]) else ""))
    print(f"no halt in {visits} visits, {cnt[0]} operations; now {s}")


# ---- The doubling map `op` of lean/Doubling.lean, with the number of machine steps of each operation ----

def op(s):
    """One operation on ('ev', c, u, v) or ('od', c, A, b); None is the halt (the same map as `op` in Lean)."""
    if s[0] == 'ev':
        _, c, u, v = s
        if 2 * u < v:
            return ('ev', c, 2 * u, v + 1)
        if v < 2 * u:
            return ('ev', c, 2 * u - v, v)
        return ('od', c, 2 * v - 3, 0)
    _, c, A, b = s
    if A == 1 and c is None:
        return None
    i = (A - 3) // 2
    if b < i:
        return ('od', c, 2 * (i - b) + 1, 2 * b + 2)
    if b == i:
        return ('od', None, 1, 2 * b + 2) if c is None else ('ev', None, c + 2 * b + 5, c + 2 * b + 7)
    r = b - i
    if c is None:
        return ('od', None, 4 * i + 11, 0) if r == 1 else ('ev', None, 2 * i + 6, 2 * i + 8) if r == 2 else \
            ('ev', 2 * i + 4, r - 2, r)
    return ('od', None, 2 * c + 4 * i + 11, 0) if r == 1 else ('ev', None, r - 1, c + i + b + 6)


def op_steps(s):
    """Machine steps charged to one operation: the steps between two visits are the sum over the operations between
    them (the halt: steps up to and including the halting step)."""
    if s[0] == 'ev':
        _, c, u, v = s
        if 2 * u < v:
            return 6 * u * u
        if v < 2 * u:
            d = v - u
            return 6 * d * d - 4 * d + 2
        return 6 * u * u - 4 * u + 5
    _, c, A, b = s
    if A == 1:
        return 2 * b + 7
    i = (A - 3) // 2
    if b <= i:
        return 6 * (b + 2) ** 2
    r = b - i
    if c is None:
        return 6 * i * i + (44 * i + 78 if r == 1 else 36 * i + 59 if r == 2 else 36 * i + 58)
    return 6 * i * i + 32 * i + 4 * c + (51 if r == 1 else 48)


def state(v):
    """The state of `op` of the visit T(c, a, b)."""
    c, a, b = v
    return ('ev', c, b + 2, a // 2 + b + 3) if a % 2 == 0 else ('od', c, a, b)


def sim_steps(c, a, b, limit=10 ** 7):
    """Direct simulation from T(c, a, b): (next visit or 'halt', number of steps)."""
    T = table()
    w = word(c, a, b)
    tape = {i: int(ch) for i, ch in enumerate(w)}
    pos, st, lo, hi = len(w), 1, 0, len(w)
    for k in range(limit):
        t = T[(st, tape.get(pos, 0))]
        if t is None:
            return "halt", k + 1
        tape[pos] = t[0]; pos += t[1]; st = t[2]
        lo = min(lo, pos)
        if pos > hi:
            hi = pos
            if st == 1:
                r = parse_t(tape, lo, pos)
                if r:
                    return r, k + 1
    return "?", limit


def check_rules():
    """`op` and `op_steps` against direct simulation: a grid of visits, and every visit of the first 3*10^6 steps."""
    bad = n = 0
    for c in (None, 0, 1, 2, 5):
        for a in range(1, 40):
            for b in range(0, 40):
                if c is not None and a == 1:
                    continue
                r, k = sim_steps(c, a, b)
                s, tot = state((c, a, b)), 0
                while True:
                    tot += op_steps(s); s = op(s)
                    if s is None or r != "halt" and s == state(r):
                        break
                n += 1
                if (s is None) != (r == "halt") or tot != k:
                    bad += 1; print("rules: differs at", c, a, b, r, k, tot)
    print(f"rules grid: {n} visits, {bad} failures")
    T = table()
    tape, pos, st, lo, hi = {}, 0, 0, 0, 0
    s, acc, nv = state(START), 7, 0
    for k in range(3 * 10 ** 6):
        t = T[(st, tape.get(pos, 0))]
        tape[pos] = t[0]; pos += t[1]; st = t[2]
        lo = min(lo, pos)
        if pos > hi:
            hi = pos
            if st == 1 and k + 1 > 7:
                r = parse_t(tape, lo, pos)
                if r is None:
                    continue
                while True:
                    acc += op_steps(s); s = op(s)
                    if s == state(r):
                        break
                nv += 1
                if acc != k + 1:
                    bad += 1; print("rules run: step count differs at step", k + 1, acc); acc = k + 1
    print(f"rules run: {nv} visits in 3e6 steps, step counts {'ok' if not bad else 'FAILED'}")
    return bad


if __name__ == "__main__":
    if sys.argv[1] == "check":
        sys.exit(1 if check() else 0)
    elif sys.argv[1] == "rules":
        sys.exit(1 if check_rules() else 0)
    elif sys.argv[1] == "checkrec":
        sys.exit(checkrec())
    elif sys.argv[1] == "events":
        events(int(float(sys.argv[2])))
    elif sys.argv[1] == "dump":
        s = START
        for _ in range(int(sys.argv[2])):
            print(-1 if s[0] is None else s[0], s[1], s[2])
            s = step(*s)
