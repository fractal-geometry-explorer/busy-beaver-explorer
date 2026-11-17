"""The block machine of lean/Macro.lean (`mstep`), transcribed, and checked against the machine.

  python3 macro.py check STEPS     compare every macro configuration of the first STEPS steps with a direct run
  python3 macro.py run N           N macro steps from the first macro configuration (the number in MacroRun.lean)
  python3 macro.py rules           the rule table (`rule`, on rows of blocks) against `mstep` and against direct
                                   simulation: a grid of configurations, and every one of the first 10^7 steps
  (the outer orbit: see outer.py)
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))

M = "1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE"
# a configuration: (X, a, m, b, t); m = None | 'z' | ('e', q) (block 2q+2); t = None | q (block 2q+3)


def norm(s, n):
    X, a, m, b, t = s
    if X == 1:
        return (0, a + 1, m, b, t), n + 2
    return s, n


def tail_next(X, k, q):
    return (X, k + 3, None, 0, None) if q == 0 else (X, k + 2, None, 0, q - 1)


def ev_next(q):
    return 'z' if q == 0 else ('e', q - 1)


def mstep(s):
    """('go', s', cost) | ('halt',) | ('stuck',), exactly as `mstep` in Macro.lean."""
    X, a, m, b, t = s
    if isinstance(m, tuple):
        q = m[1]
        if X >= 3:
            return ('go',) + norm((X - 2, a + 2, ev_next(q), b, t), 6 * a + 18)
        if X == 0:
            return ('go', (0, a + 2, ev_next(q), b, t), 6 * a + 14)
        return ('stuck',)
    if m is None and t is not None:
        q = t
        if X == 2:
            if a + b == 0:
                return ('go', (5, 0, ('e', q), 0, None), 15)
            return ('go', (5, 0, 'z', a + b - 1, q), 15)
        if X >= 3:
            return ('go',) + norm(tail_next(X - 2, a + b, q), 6 * (a + b) + 18)
        if X == 0:
            return ('go', tail_next(0, a + b, q), 6 * (a + b) + 14)
        return ('stuck',)
    if m is None:
        if X == 2:
            return ('stuck',) if a + b == 0 else ('go', (5, 0, 'z', a + b - 1, None), 15)
        if X >= 5:
            return ('go',) + norm((X - 4, 0, None, 0, a + b + 1), 6 * (a + b) + 20)
        if X == 4:
            return ('halt',)
        if X == 0:
            return ('go', (2 * (a + b) + 4, 0, None, 0, 0), 8 * (a + b) + 27)
        if X == 3:
            return ('go', (2 * (a + b) + 6, 0, None, 0, 0), 8 * (a + b) + 35)
        return ('stuck',)
    # m == 'z'
    if X >= 5:
        if b >= 1:
            return ('go',) + norm((X - 4, 0, ('e', a + 2), b - 1, t), 6 * a + 20)
        if t is not None:
            return ('go',) + norm((X - 4, 0, ('e', a + t + 3), 0, None), 6 * a + 20)
        return ('go',) + norm((X - 4, 0, None, 0, a + 1), 6 * a + 20)
    if X in (0, 3):
        k = a + 1 if X == 3 else a
        if b >= 2:
            return ('go', (2 * k + 7, 0, 'z', b - 2, t), 8 * k + 20)
        if b == 1 and t is not None:
            return ('go', (2 * k + 7, 0, ('e', t), 0, None), 8 * k + 20)
        if b == 1:
            return ('go', (2 * k + 5, 0, None, 0, 0), 8 * k + 28)
        if t is not None:
            return ('go', (2 * k + 2 * t + 7, 0, None, 0, 0), 8 * k + 2 * t + 30)
        return ('go', (2 * k + 4, 0, None, 0, 0), 8 * k + 27)
    return ('stuck',)


S0 = (10, 0, None, 0, 0)
T0 = 102


def tape(s):
    """cells of cfg s from the left end of the left block; head index"""
    X, a, m, b, t = s
    c = [1] * X + [0, 0] + [1, 0] * a
    if m == 'z':
        c += [0]
    elif isinstance(m, tuple):
        c += [1] * (2 * m[1] + 2) + [0]
    c += [1, 0] * b
    if t is not None:
        c += [1] * (2 * t + 3)
    return c, X


def check(steps):
    from bbtools.machine import Machine, Run
    r = Run(Machine.parse(M))
    s, t, n = S0, T0, 0
    r.run(T0)
    while t < steps:
        res = mstep(s)
        assert res[0] == 'go', res
        s2, cost = res[1], res[2]
        r.run(t + cost)
        t += cost
        c, h = tape(s2)
        lo = r.head - h
        cells = r.tape.word(min(lo, r.tape.lo), max(r.tape.hi, lo + len(c) - 1))
        off = lo - min(lo, r.tape.lo)
        assert r.state == 5 and all(v == 0 for v in cells[:off]) and cells[off:off + len(c)] == c \
            and all(v == 0 for v in cells[off + len(c):]), (t, s2)
        s, n = s2, n + 1
    print(f"agree: {n} macro configurations, every cell and the step count, up to step {t}")


def run(N):
    s, t = S0, T0
    for i in range(N):
        res = mstep(s)
        if res[0] != 'go':
            print('macro', res[0], 'at macro step', i, 'machine step', t)
            return
        s, t = res[1], t + res[2]
    print(f"{N} macro steps: configuration {s}, machine step {t}")


# ---- The rule table: mstep written on exact tapes C(X; R) = 0^inf 1^X F> 0 0 R 0^inf, R a row of blocks 1^y 0 ----

def blocks(s):
    """The row of blocks right of the gap of cfg s (block lengths; the last one may be the tail)."""
    X, a, m, b, t = s
    r = [1] * a + ([0] if m == 'z' else [2 * m[1] + 2] if isinstance(m, tuple) else []) + [1] * b
    return (X, r + ([2 * t + 3] if t is not None else []))


def walk1(X, r, n):
    """X - 2 or X - 4 can be 1: two more steps walk that 1 over the gap, where it becomes a unit."""
    return (0, [1] + r, n + 2) if X == 1 else (X, r, n)


def rule(X, r):
    """One rule of the table on C(X; r): (X', r', steps) or ('halt', steps).  r: block lengths."""
    while r and r[-1] == 0:
        r = r[:-1]
    k = 0
    while k < len(r) and r[k] == 1:
        k += 1
    if X == 2:
        return (5, [r[0] - 1] + r[1:], 15)                                  # the first block loses a 1
    if k < len(r) and r[k] >= 2:                                           # a round against the block Y = r[k]
        r2 = [1] * (k + 2) + [r[k] - 2] + r[k + 1:]
        return walk1(X - 2, r2, 6 * k + 18) if X >= 3 else (0, r2, 6 * k + 14)
    Z, rest = (r[k + 1], r[k + 2:]) if k + 1 < len(r) else (0, [])     # a gap (or the end) after k units
    if X >= 5:                                                             # merge
        return walk1(X - 4, [2 * k + Z + 5] + rest, 6 * k + 20)
    if X == 4:
        return ('halt', 6 * k + 18)
    kk = k + 1 if X == 3 else k                                            # restart (X = 0 or 3)
    if rest:
        return (2 * kk + 7, [rest[0] - 1] + rest[1:], 8 * kk + 20)        # here Z = 1
    return (2 * kk + Z + 4, [3], 8 * kk + Z + 27)                          # at the end: an outer configuration


def cells(X, r):
    c = [1] * X + [0, 0]
    for y in r:
        c += [1] * y + [0]
    return c, X


def inv(s):
    X, a, m, b, t = s
    return X != 1 and not (X % 2 == 0 and X != 0 and m is not None) and not (X == 2 and a + b == 0 and t is None)


TBL = {}
for _i, _g in enumerate(M.split("_")):
    for _v in (0, 1):
        _t = _g[3 * _v:3 * _v + 3]
        TBL[(_i, _v)] = None if _t[0] == "-" else (int(_t[0]), 1 if _t[1] == "R" else -1, ord(_t[2]) - 65)


def run_cells(c, h, st, n):
    """n steps of the machine; ('halt', step) if it halts first, else (tape dict, head, state)."""
    tape = {i: v for i, v in enumerate(c) if v}
    for i in range(n):
        tr = TBL[(st, tape.get(h, 0))]
        if tr is None:
            return 'halt', i + 1
        if tr[0]:
            tape[h] = 1
        else:
            tape.pop(h, None)
        h += tr[1]; st = tr[2]
    return tape, h, st


def same(tape, h, st, X, r):
    c, hc = cells(X, r)
    return st == 5 and sorted(i - h for i in tape) == [i - hc for i, v in enumerate(c) if v]


def check_rules():
    bad = n = halts = 0
    for X in range(0, 25):
        for a in range(7):
            for m in [None, 'z'] + [('e', q) for q in range(4)]:
                for b in range(6):
                    for t in [None] + list(range(4)):
                        s = (X, a, m, b, t)
                        if not inv(s):
                            continue
                        n += 1
                        res = mstep(s)
                        u = rule(*blocks(s))
                        if res[0] == 'halt':
                            halts += 1
                            ok = u[0] == 'halt' and run_cells(*cells(*blocks(s)), 5, u[1]) == ('halt', u[1])
                        else:
                            X2, r2 = blocks(res[1])
                            ok = u[0] != 'halt' and (u[0], [y for y in u[1]]) == (X2, r2 + [0] * (len(u[1]) - len(r2))) \
                                and u[2] == res[2]
                            if ok:
                                tp = run_cells(*cells(*blocks(s)), 5, u[2])
                                ok = tp[0] != 'halt' and same(*tp, u[0], u[1])
                        if not ok:
                            bad += 1; print("differs at", s, res, u)
    print(f"rules grid: {n} configurations ({halts} halting), {bad} failures")
    N = 10 ** 7
    x, due, nv = (10, [3]), 102, 0
    tape, h, st = {}, 0, 0
    for i in range(1, N + 1):
        tr = TBL[(st, tape.get(h, 0))]
        if tr[0]:
            tape[h] = 1
        else:
            tape.pop(h, None)
        h += tr[1]; st = tr[2]
        if i == due:
            nv += 1
            if not same(tape, h, st, *x):
                bad += 1; print("run differs at step", i, x); break
            y = rule(*x)
            x, due, last = (y[0], y[1]), due + y[2], i
    print(f"rules run: {nv} configurations C(X; R) in the first {N:.0e} steps, the last at step {last}, "
          f"{'each at the predicted step' if not bad else 'FAILED'}")
    return bad


if __name__ == "__main__":
    if sys.argv[1] == "check":
        check(int(float(sys.argv[2])))
    elif sys.argv[1] == "rules":
        sys.exit(1 if check_rules() else 0)
    elif sys.argv[1] == "run":
        run(int(float(sys.argv[2])))
