"""The block machine of lean/Macro.lean (`mstep`), transcribed, and checked against the machine.

  python3 macro.py check STEPS     compare every macro configuration of the first STEPS steps with a direct run
  python3 macro.py run N           N macro steps from the first macro configuration (the number in MacroRun.lean)
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


if __name__ == "__main__":
    if sys.argv[1] == "check":
        check(int(float(sys.argv[2])))
    elif sys.argv[1] == "run":
        run(int(float(sys.argv[2])))
