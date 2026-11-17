"""The rules of a round with exact step counts (lean/Rules.lean, lean/Round.lean), checked against direct simulation.

    E(m, k)    := 0^inf D> 110 (10)^m (110)^k 0^inf                       (end of a round)
    S(u, y, k) := 0^inf B> 1110 (101010)^u 10 110 (10)^y (110)^k 0^inf    (in a round)

usage: python3 py/exact.py          # every rule on a grid of tapes, and the run from blank tape
"""
import re
import sys

TM = "1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC"

# ---- direct simulation (independent of the rules) ----

def table(tm):
    """'1RB0RE_...' -> {(state, read): (write, move, next state) or None}."""
    T = {}
    for i, part in enumerate(tm.split('_')):
        for r in (0, 1):
            t = part[3 * r:3 * r + 3]
            T[('ABCDEF'[i], r)] = None if t[2] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, t[2])
    return T


def canon(cells, pos, st):
    """A configuration as (state, word, head offset), the word with the blanks at both ends stripped."""
    ks = [k for k, v in cells.items() if v]
    if not ks:
        return (st, '', 0)
    lo, hi = min(ks), max(ks)
    return (st, ''.join(str(cells.get(k, 0)) for k in range(lo, hi + 1)), pos - lo)


def cfg(left, st, right):
    """The configuration 0^inf left S> right 0^inf (head on the first symbol of right)."""
    cells = {i: int(c) for i, c in enumerate(left + right)}
    return cells, len(left), st


def run(T, c, n):
    """Run n steps from c = (cells, pos, st). Returns ('ok', c) or ('halt', k) if the k-th step (k <= n) is a halt."""
    cells, pos, st = dict(c[0]), c[1], c[2]
    for k in range(1, n + 1):
        t = T[(st, cells.get(pos, 0))]
        if t is None:
            return 'halt', k
        cells[pos] = t[0]; pos += t[1]; st = t[2]
    return 'ok', (cells, pos, st)


def E(m, k):
    return cfg('', 'D', '110' + '10' * m + '110' * k)


def S(u, y, k):
    return cfg('', 'B', '1110' + '101010' * u + '10110' + '10' * y + '110' * k)


def tape(s):
    return E(*s[1:]) if s[0] == 'E' else S(*s[1:])


def rule(s):
    """(name, next family configuration or 'halt', steps)."""
    if s[0] == 'S':
        _, u, y, k = s
        if u >= 1:
            return 'sweep', ('S', u - 1, y + 4, k), 30 * (u - 1) + 64
        return 'finish', ('E', y + 4, k), 38
    _, m, k = s
    t, r = divmod(m, 3)
    if r == 1:
        return 'start1', ('S', t, 0, k + 1), 6 * k + 30 * t + 57
    if r == 2:
        if k == 0:
            return 'to_halt', 'halt', 10 * t + 38           # 10t + 37 steps to F on a 0, then the halting step
        return 'start2', ('S', t, 1, k + 1), 6 * (k - 1) + 30 * t + 75
    t -= 1                                                  # m = 3t + 3, m >= 3
    if k >= 1:
        return 'start0', ('S', t, 4, k - 1), 30 * t + 77
    return 'start0z', ('S', t, 4, 0), 60 * t + 143


def family(cells, pos, st):
    """The family configuration this is, or None."""
    if st not in 'DB' or any(v for i, v in cells.items() if i < pos):
        return None
    w = canon(cells, pos, st)
    if w[2] != 0:
        return None
    w = w[1]
    if st == 'D':
        x = re.fullmatch(r'110((?:10)*)((?:110)*)', w) or re.fullmatch(r'110((?:10)*)((?:110)*)', w + '0')
        return x and ('E', len(x.group(1)) // 2, len(x.group(2)) // 3)
    pat = r'1110((?:101010)*)10110((?:10)*)((?:110)*)'
    x = re.fullmatch(pat, w) or re.fullmatch(pat, w + '0')
    return x and ('S', len(x.group(1)) // 6, len(x.group(2)) // 2, len(x.group(3)) // 3)


def first_family(T, c, n):
    cells, pos, st = dict(c[0]), c[1], c[2]
    for k in range(1, n + 1):
        t = T[(st, cells.get(pos, 0))]
        if t is None:
            return 'halt', k
        cells[pos] = t[0]; pos += t[1]; st = t[2]
        if cells.get(pos, 0) == 1 and st in 'DB':
            f = family(cells, pos, st)
            if f:
                return f, k
    return '?', n


def main():
    T = table(TM)
    bad = n = 0
    counts = {}
    grid = [('E', m, k) for m in range(1, 61) for k in range(0, 12)] + \
           [('S', u, y, k) for u in range(0, 20) for y in range(0, 15) for k in range(0, 6)]
    for s in grid:
        name, t, N = rule(s)
        if name in ('start0', 'start0z'):
            # Lean's start0', start0z' pass one S configuration on the way: S(t + 1, 0, k), then a sweep
            tt = (s[1] - 3) // 3
            via = (('S', tt + 1, 0, max(s[2] - 1, 0)), 13 if name == 'start0' else 30 * tt + 79)
            r2, c = run(T, tape(s), N)
            ok = first_family(T, tape(s), N) == via and r2 == 'ok' and canon(*c) == canon(*tape(t))
            r, k = via
        else:
            r, k = first_family(T, tape(s), N)
            ok = (r == t and k == N)
        n += 1
        counts[name] = counts.get(name, 0) + 1
        if not ok:
            bad += 1
            print("differs:", s, name, t, N, r, k)
    # the sweeps of a round together: S(u, y, k) -> E(y + 4u + 4, k) in 15u^2 + 49u + 38 steps
    for u in range(0, 30):
        for y in (0, 1, 4):
            for k in (0, 2):
                r, c = run(T, S(u, y, k), 15 * u * u + 49 * u + 38)
                n += 1
                counts['sweeps+finish'] = counts.get('sweeps+finish', 0) + 1
                if r != 'ok' or canon(*c) != canon(*E(y + 4 * u + 4, k)):
                    bad += 1
                    print("sweeps differ:", u, y, k)
    print(f"grid: {n} tapes, each run to its first E or S configuration or the halt "
          f"({', '.join(f'{k} {v}' for k, v in sorted(counts.items()))}), {bad} failures")
    LIMIT = 10 ** 7
    cells, pos, st = {}, 0, 'A'
    s, at, nv, ne, k, runbad = ('E', 8, 1), 280, 0, 0, 0, 0
    while at <= LIMIT:
        while k < at:
            t = T[(st, cells.get(pos, 0))]
            cells[pos] = t[0]; pos += t[1]; st = t[2]; k += 1
        nv += 1
        ne += s[0] == 'E'
        if canon(cells, pos, st) != canon(*tape(s)):
            runbad = 1
            print("run differs at step", at, s)
            break
        last = (s, at)
        _, s, N = rule(s)
        at += N
    print(f"run from blank: {nv} family configurations ({ne} round ends E) at their predicted step counts up to "
          f"step {LIMIT:,} (the last {last[0][0]}{last[0][1:]} at step {last[1]:,}), {'ok' if not runbad else 'FAILED'}")
    s, tot = ('E', 7, 0), 0
    while s != 'halt':
        tot += rule(s)[2]; s = rule(s)[1]
    print("E(7, 0) -> halt:", tot, "steps by the rules,", run(T, E(7, 0), 10 ** 5), "by simulation")
    return bad + runbad


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
