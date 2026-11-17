"""The rules of the map F (lean/Map.lean) on exact tapes, with the number of machine steps of each, checked against
direct simulation.

    python3 py/exact.py          # every rule on a grid of tapes, and every node of the first 10^7 steps from blank tape

The tapes (Lean: S, Pc, Qc, Tc, Oc in lean/Map.lean and lean/Doubling.lean):

    S(x)       = 0^inf 1^x 1110 B> 0^inf
    P(k, m)    = 0^inf F> 0 0 (10)^k 1^m 0 1 0^inf
    Q(u, n)    = 0^inf F> 0 0 (10)^3 (1110)^u 1^n 0 1 0^inf                      (n odd)
    T(u, v)    = 0^inf F> 0 0 (10)^3 (1110)^u 1111 0 (10)^v 0 1 0^inf
    O(p, i, r) = 0^inf 1^6 0 (10)^p (1111)^i F> 1 0 1^r 0 1 0^inf                 (inside an overflow, r < 2)
"""
import sys

M = "1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA"
T = {}
for _i, _g in enumerate(M.split("_")):
    for _b in (0, 1):
        _t = _g[3 * _b:3 * _b + 3]
        T[(_i, _b)] = None if _t[0] == "-" else (int(_t[0]), 1 if _t[1] == "R" else -1, ord(_t[2]) - 65)
B, F = 1, 5


def rule(x):
    """One rule: (next tape or 'halt', machine steps; the halt counts the halting step)."""
    f = x[0]
    if f == 'S':
        return ('P', 3, x[1]), x[1] + 29
    if f == 'P':
        _, k, m = x
        if m >= 2 * k + 3:
            return ('P', 2 * k + 3, m - 2 * k - 3), 4 * k * k + 8 * k + 21
        if m == 0:
            return 'halt', 2 * k + 14
        if m == 1:
            return (('S', 2 * k + 7), 9 * k + 41) if k % 2 else (('Q', k // 2, 3), 5 * k + 47)
        if m == 2:
            return (('T', (k - 1) // 2, 1), 5 * k + 50) if k % 2 else (('S', 2 * k + 9), 9 * k + 44)
        i, r = (m - 3) // 2, (m - 3) % 2
        return ('O', k - 1 - i, i, r), 4 * i * i + 2 * i + 2 * k + 15
    if f == 'O':
        _, p, i, r = x
        if p == 0:
            return (('S', 4 * i + 13), 16 * i + 43) if r else (('S', 4 * i + 7), 8 * i + 6)
        if p % 2:
            q = (p - 1) // 2
            return (('T', q, 2 * i + 3), 12 * i + 6 * q + 48) if r else (('P', 2 * q + 6, 4 * i + 2), 12 * i + 18 * q + 55)
        q = (p - 2) // 2
        return (('S', 4 * q + 4 * i + 17), 16 * i + 14 * q + 57) if r else (('Q', q + 1, 4 * i + 7), 12 * i + 6 * q + 48)
    if f == 'Q':
        _, u, n = x
        if n >= 9:
            return ('P', 2 * u + 9, n - 9), 28 * u + 81
        return {1: (('S', 4 * u + 13), 16 * u + 68), 3: (('Q', 1, 4 * u + 7), 12 * u + 69),
                5: (('P', 6, 4 * u + 6), 20 * u + 94), 7: (('S', 4 * u + 15), 24 * u + 63)}[n]
    _, u, v = x
    return ('Q', 1, 4 * u + 2 * v + 9), 12 * u + 4 * v + 73


def cfg(x):
    """(cells, head index, state) of a tape."""
    f = x[0]
    if f == 'S':
        w = "1" * x[1] + "1110"
        return w, len(w), B
    if f == 'P':
        return "00" + "10" * x[1] + "1" * x[2] + "01", 0, F
    if f == 'Q':
        return "00" + "10" * 3 + "1110" * x[1] + "1" * x[2] + "01", 0, F
    if f == 'T':
        return "00" + "10" * 3 + "1110" * x[1] + "1111" + "0" + "10" * x[2] + "01", 0, F
    left = "111111" + "0" + "10" * x[1] + "1111" * x[2]
    return left + "10" + "1" * x[3] + "01", len(left), F


def ones(tape, h):
    return sorted(i - h for i, v in tape.items() if v)


def is_cfg(tape, h, st, x):
    w, hx, sx = cfg(x)
    return st == sx and ones(tape, h) == [i - hx for i, c in enumerate(w) if c == "1"]


def check_one(x):
    """Run the machine from x for the stated number of steps: True if it is then exactly at the stated target (or
    halts exactly then, for the halt row) and has not halted before."""
    y, n = rule(x)
    w, h, st = cfg(x)
    tape = {i: int(c) for i, c in enumerate(w)}
    for t in range(n):
        tr = T[(st, tape.get(h, 0))]
        if tr is None:
            return y == 'halt' and t + 1 == n
        tape[h] = tr[0]; h += tr[1]; st = tr[2]
    return y != 'halt' and is_cfg(tape, h, st, y)


def grid():
    xs = [('S', x) for x in range(6, 61)]
    xs += [('P', k, m) for k in range(3, 31) for m in range(0, 81)]
    xs += [('O', p, i, r) for p in range(0, 21) for i in range(0, 21) for r in (0, 1)]
    xs += [('Q', u, n) for u in range(1, 21) for n in range(1, 42, 2)]
    xs += [('T', u, v) for u in range(0, 21) for v in range(1, 21)]
    return xs


def main():
    bad = halts = 0
    xs = grid()
    for x in xs:
        if not check_one(x):
            bad += 1; print("rule differs at", x, rule(x))
        halts += rule(x)[0] == 'halt'
    print(f"rules grid: {len(xs)} tapes ({halts} halting), {bad} failures")
    N = 10 ** 7
    x, due, nv = ('S', 13), 110, 0
    tape, h, st = {}, 0, 0
    for t in range(1, N + 1):
        tr = T[(st, tape.get(h, 0))]
        tape[h] = tr[0]; h += tr[1]; st = tr[2]
        if t == due:
            nv += 1
            if not is_cfg(tape, h, st, x):
                bad += 1; print("run differs at step", t, x); break
            x, n = rule(x)
            due += n
    print(f"rules run: {nv} tapes of the families in the first {N:.0e} steps, the last at step {due - n}, "
          f"{'each at the predicted step' if not bad else 'FAILED'}")
    return bad


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
