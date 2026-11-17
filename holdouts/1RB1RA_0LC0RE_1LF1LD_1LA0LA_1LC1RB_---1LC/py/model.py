"""The three-level counter of 1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC.

At every moment the head reaches a new cell on the right in state B the tape is

    S(c, a, b) = 0^inf (10)^c 1^a 0 (10)^b 1 B>0 0^inf          (a even, a >= 2)

and the next such moment is given by `step` (an "odometer" with three wheels):

    2b < a           -> (c, a - 2b, 2b + 1)                          the (10)^b block doubles, eating the 1s
    2b >= a, c >= 1  -> step(c - 1, 2a + 4, max(b - a/2 - 1, 0))     carry: one 10 of the left block becomes 1s
    2b >= a, c = 0   -> halt if b = a/2, else step(a, 4, b - a/2 - 1) reset: the 1s become the new left block

With u = b + 1 and v = a/2 + b + 2 (so a = 2(v - u - 1)) the odometer is a doubling map with a growing modulus
(`op`; one operation is a doubling step or a carry):

    2u < v           u <- 2u,      v <- v + 1                       a visit S
    2u > v, c >= 1   u <- 2u - v,  v <- v + 1,  c <- c - 1          carry
    2u = v, c >= 1   u <- 1,       v <- v + 2,  c <- c - 1          carry that empties the fast wheel
    2u > v, c = 0    c <- 2(v - u - 1),  u <- 2u - v,  v <- u + 3   reset
    2u = v, c = 0    halt

    python3 py/model.py check        # the rule against direct simulation (c < 6, a < 30, b < 34) and the run (3e6 steps);
                                     # the doubling map against the rule (200,000 visits of the run)
    python3 py/model.py rules        # the sweep rules of lean/Map.lean with their step counts, against direct simulation
    python3 py/model.py resets 1e8   # the resets of the run, from S(0, 4, 1) at step 43
    python3 py/model.py dump 3000    # the first visits "c a b", same output as `c/odo 1000000000 dump 3000` (c/odo.c is `op` in C)
"""
import re
import sys

M = "1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC"


def step(c, a, b):
    while True:
        if 2 * b < a:
            return (c, a - 2 * b, 2 * b + 1)
        if c >= 1:
            c, a, b = c - 1, 2 * a + 4, max(b - a // 2 - 1, 0)
            continue
        if b == a // 2:
            return "halt"
        c, a, b = a, 4, b - a // 2 - 1


def op(c, u, v):
    """One operation of the doubling map: (c, u, v, kind) with kind in visit, carry, reset; or "halt"."""
    t = 2 * u
    if t < v:
        return (c, t, v + 1, "visit")
    if c:
        return (c - 1, t - v, v + 1, "carry") if t > v else (c - 1, 1, v + 2, "carry")
    if t > v:
        return (2 * (v - u - 1), t - v, t - v + 3, "reset")
    return "halt"


def visits(n):
    """The first n visits (c, a, b) of the run, by the doubling map."""
    c, u, v = 0, 2, 5
    out = [(c, 2 * (v - u - 1), u - 1)]
    while len(out) < n:
        r = op(c, u, v)
        if r == "halt":
            out.append("halt"); break
        c, u, v, kind = r
        if kind == "visit":
            out.append((c, 2 * (v - u - 1), u - 1))
    return out


def table():
    T = {}
    for i, g in enumerate(M.split("_")):
        for s in (0, 1):
            t = g[3 * s:3 * s + 3]
            T[(i, s)] = None if t[0] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
    return T


PAT = re.compile(r"((?:10)*)(1*)0((?:10)*)1")


def parse_s(tape, lo, pos):
    a = lo
    while a < pos and tape.get(a, 0) == 0:
        a += 1
    m = PAT.fullmatch("".join(str(tape.get(x, 0)) for x in range(a, pos)))
    return None if not m else (len(m.group(1)) // 2, len(m.group(2)), len(m.group(3)) // 2)


def sim(c, a, b, limit=10 ** 6, count=False):
    """Direct simulation from S(c, a, b) to the next visit or the halt (with count: and the number of steps)."""
    T = table()
    w = "10" * c + "1" * a + "0" + "10" * b + "1"
    tape = {i: int(ch) for i, ch in enumerate(w)}
    pos, st, lo, hi = len(w), 1, 0, len(w)
    for i in range(limit):
        t = T[(st, tape.get(pos, 0))]
        if t is None:
            return ("halt", i + 1) if count else "halt"
        tape[pos] = t[0]; pos += t[1]; st = t[2]
        lo = min(lo, pos)
        if pos > hi:
            hi = pos
            if st == 1:
                r = parse_s(tape, lo, pos)
                if r:
                    return (r, i + 1) if count else r
    return "?"


def check():
    bad = n = 0
    for c in range(6):
        for a in range(2, 30, 2):
            for b in range(34):
                n += 1
                if sim(c, a, b) != step(c, a, b):
                    bad += 1
    print(f"grid: {n} configurations, {bad} mismatches")
    T = table()
    tape, pos, st, lo, hi, prev, k = {}, 0, 0, 0, 0, None, 0
    for k in range(3 * 10 ** 6):
        t = T[(st, tape.get(pos, 0))]
        tape[pos] = t[0]; pos += t[1]; st = t[2]
        lo = min(lo, pos)
        if pos > hi:
            hi = pos
            if st == 1:
                r = parse_s(tape, lo, pos)
                if r:
                    if prev is not None and step(*prev) != r:
                        print("run mismatch at", k + 1, prev, r); bad += 1
                    elif prev is None:
                        print("first S", r, "at step", k + 1)
                    prev = r; n += 1
    print("run: ok" if not bad else f"{bad} mismatches")
    s, nv = (0, 4, 1), 0
    for v in visits(200000):
        if v != s:
            print("doubling map differs at visit", nv, v, s); bad += 1; break
        s = step(*s); nv += 1
    print(f"doubling map: {nv} visits agree with the rule")
    return bad


def resets(maxsteps):
    c, a, b = 0, 4, 1
    n = r = 0
    while n < maxsteps:
        n += 1
        while True:
            if 2 * b < a:
                c, a, b = c, a - 2 * b, 2 * b + 1; break
            if c >= 1:
                c, a, b = c - 1, 2 * a + 4, max(b - a // 2 - 1, 0); continue
            if b == a // 2:
                print("halt at macro step", n); return
            r += 1
            print(f"reset {r} at macro step {n}: new left block c = {a}, b - a/2 = {b - a // 2}")
            c, a, b = a, 4, b - a // 2 - 1
    print(f"{n} macro steps, {r} resets, no halt; now c = {c}, a = {a}, b = {b}")


# ---- The sweep rules of lean/Map.lean (`inner`, `F`) with the step counts of lean/Rules.lean ----
# ('S', c, a, b):    0^inf (10)^c 1^a 0 (10)^b 1 B> 0^inf                    (a visit; Lean `S c p b`, a = 2p + 2)
# ('R', c, p, k, z): 0^inf (10)^c 1^(2p) A> 1 0 1^(4k+1) 0 (10)^z 1111 0^inf   (inside a sweep; Lean `Rc c p k z`)

def rule(x):
    """One rule: (next configuration or 'halt', machine steps; the halt counts the halting step)."""
    if x[0] == 'S':
        _, c, a, b = x
        return (('S', c, a, 1), 24) if b == 0 else (('R', c, a // 2 - 1, 0, b - 1), 4 * (b - 1) + 22)
    _, c, p, k, z = x
    if p >= 1:
        return (('R', c, p - 1, k + 1, z - 1), 8 * k + 8) if z >= 1 else (('S', c, 2 * p, 2 * k + 3), 12 * k + 18)
    if c >= 1:
        if z >= 3:
            return ('R', c - 1, 2 * k + 2, 1, z - 3), 12 * k + 22
        return [(('S', c - 1, 4 * k + 8, 1), 12 * k + 36), (('S', c - 1, 4 * k + 8, 1), 12 * k + 20),
                (('S', c - 1, 4 * k + 6, 3), 12 * k + 32)][z]
    if z >= 2:
        return ('R', 2 * k + 2, 1, 0, z - 2), 12 * k + 20
    return (('S', 2 * k + 2, 4, 1), 12 * k + 26) if z == 1 else ('halt', 16 * k + 31)


def config(x):
    """The configuration as (tape dict, head position, state)."""
    if x[0] == 'S':
        _, c, a, b = x
        w, st, head = "10" * c + "1" * a + "0" + "10" * b + "1", 1, None
    else:
        _, c, p, k, z = x
        left, right = "10" * c + "1" * (2 * p), "10" + "1" * (4 * k + 1) + "0" + "10" * z + "1111"
        w, st, head = left + right, 0, len(left)
    return {i: int(ch) for i, ch in enumerate(w)}, len(w) if head is None else head, st


def same(t1, p1, t2, p2):
    """Equal tapes up to a shift, with the heads at the same cell."""
    o1 = sorted(i - p1 for i, v in t1.items() if v)
    o2 = sorted(i - p2 for i, v in t2.items() if v)
    return o1 == o2


def run_rule(x):
    """Direct simulation of one rule from x: 'ok' if after the stated number of steps the machine is exactly at the
    stated target (or halts exactly then), with no halt and, for a visit target, no visit of the right end before."""
    T = table()
    y, n = rule(x)
    tape, pos, st = config(x)
    hi = max(tape) if tape else 0
    lo = 0
    for i in range(n):
        t = T[(st, tape.get(pos, 0))]
        if t is None:
            return y == 'halt' and i + 1 == n
        tape[pos] = t[0]; pos += t[1]; st = t[2]
        lo = min(lo, pos)
        if pos > hi:
            hi = pos
            if st == 1 and i + 1 < n and y != 'halt' and y[0] == 'S' and parse_s(tape, lo, pos):
                return False
    if y == 'halt':
        return False
    t2, p2, s2 = config(y)
    return st == s2 and same(tape, pos, t2, p2)


def to_visit(x):
    """Apply rules from x until a visit or the halt: (target, total steps)."""
    tot = 0
    while True:
        x, n = rule(x)
        tot += n
        if x == 'halt' or x[0] == 'S':
            return x, tot


def check_rules():
    bad = n = 0
    for c in range(5):
        for p in range(8):
            for k in range(8):
                for z in range(10):
                    n += 1
                    if not run_rule(('R', c, p, k, z)):
                        bad += 1; print("rule differs at R", c, p, k, z, rule(('R', c, p, k, z)))
    for c in range(5):
        for a in range(2, 20, 2):
            for b in range(12):
                n += 1
                if not run_rule(('S', c, a, b)):
                    bad += 1; print("rule differs at S", c, a, b)
    print(f"rules, one at a time: {n} configurations, {bad} failures")
    m = halts = 0
    for c in range(6):
        for a in range(2, 30, 2):
            for b in range(34):
                y, tot = to_visit(('S', c, a, b))
                r = sim(c, a, b, limit=10 ** 6, count=True)
                m += 1; halts += y == 'halt'
                if (y if y == 'halt' else y[1:], tot) != r:
                    bad += 1; print("visit to visit differs at", c, a, b, y, tot, r)
                u, v = b + 1, a // 2 + b + 2
                if 2 * u < v and tot != 4 * u * u + 4 * u + 16:
                    bad += 1; print("doubling count differs at", c, a, b)
    print(f"rules, visit to next visit: {m} visits ({halts} halting), {bad} failures")
    T = table()
    tape, pos, st, lo, hi = {}, 0, 0, 0, 0
    x, acc, nv, N = ('S', 0, 4, 1), 43, 0, 10 ** 7
    for k in range(N):
        t = T[(st, tape.get(pos, 0))]
        tape[pos] = t[0]; pos += t[1]; st = t[2]
        lo = min(lo, pos)
        if pos > hi:
            hi = pos
            if st == 1:
                r = parse_s(tape, lo, pos)
                if r is None:
                    continue
                if nv:
                    x, s = to_visit(x); acc += s
                nv += 1
                if x[1:] != r or acc != k + 1:
                    bad += 1; print("run differs at step", k + 1, x, acc, r); x, acc = ('S',) + r, k + 1
    print(f"rules, run from blank tape: {nv} visits in the first {N:.0e} steps, last at step {acc}, "
          f"{'all at the predicted step' if not bad else 'FAILED'}")
    return bad


if __name__ == "__main__":
    if sys.argv[1] == "check":
        sys.exit(1 if check() else 0)
    if sys.argv[1] == "rules":
        sys.exit(1 if check_rules() else 0)
    if sys.argv[1] == "dump":
        for v in visits(int(sys.argv[2])):
            print(*v)
        sys.exit(0)
    resets(int(float(sys.argv[2])))
