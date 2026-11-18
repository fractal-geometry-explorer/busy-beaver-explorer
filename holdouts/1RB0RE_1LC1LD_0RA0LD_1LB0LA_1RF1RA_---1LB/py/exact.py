"""The rule table with exact step counts (lean/Rules.lean), checked against direct simulation.

    D(k, y, z) := 0^inf (01)^(k+1) D> 1^(y+1) (10)^z 1 0^inf
    A(m, z)    := 0^inf A> 1^m (10)^z 1 0^inf

usage: python3 py/exact.py          # every rule on a grid of tapes, and the run from blank tape
"""
import sys

TM = "1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB"

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


def D(k, y, z):
    return cfg('01' * (k + 1), 'D', '1' * (y + 1) + '10' * z + '1')


def A(m, z):
    return cfg('', 'A', '1' * m + '10' * z + '1')


# ---- the rules: one rule applied to a family configuration, with its number of steps ----

def rule(s):
    """s = ('D', k, y, z) or ('A', m, z). Returns (name, next family configuration or 'halt', steps)."""
    if s[0] == 'D':
        _, k, y, z = s
        if k >= 1:
            return 'd_step', ('D', k - 1, y + 3, z), 4 * (k - 1) + 15
        return 'd_zero', ('A', y + 3, z), 8
    _, m, z = s
    if m % 2 == 1:
        i = (m - 1) // 2
        if z >= 1:
            return 'a_odd', ('D', i, 0, z - 1), 2 * i + 4
        return 'reset_odd', ('D', 0, 0, i + 1), 6 * i + 16
    i = (m - 2) // 2
    if z >= 2:
        return 'a_even', ('D', i + 2, 0, z - 2), 6 * i + 19
    if z == 1:
        return 'reset_even', ('D', 0, 0, i + 3), 10 * i + 39
    return 'halt_even', 'halt', 2 * i + 5    # 2i + 4 steps to F on a 0, then the halting step


def tape(s):
    return D(*s[1:]) if s[0] == 'D' else A(*s[1:])


def main():
    T = table(TM)
    bad = n = 0
    counts = {}
    grid = [('D', k, y, z) for k in range(0, 25) for y in range(0, 12) for z in range(0, 6)] + \
           [('A', m, z) for m in range(1, 60) for z in range(0, 12)]
    for s in grid:
        name, t, N = rule(s)
        r, c = run(T, tape(s), N)
        ok = (r == 'halt' and c == N) if t == 'halt' else (r == 'ok' and canon(*c) == canon(*tape(t)))
        n += 1
        counts[name] = counts.get(name, 0) + 1
        if not ok:
            bad += 1
            print("differs:", s, name, t, N, r)
    # the sweep D(k, y, z) -> A(y + 3k + 3, z): k times d_step, then d_zero, 2k^2 + 13k + 8 steps in all
    for k in range(0, 40):
        for y in (0, 1, 5):
            for z in (0, 1, 3):
                r, c = run(T, D(k, y, z), 2 * k * k + 13 * k + 8)
                n += 1
                counts['sweep'] = counts.get('sweep', 0) + 1
                if r != 'ok' or canon(*c) != canon(*A(y + 3 * k + 3, z)):
                    bad += 1
                    print("sweep differs:", k, y, z)
    print(f"grid: {n} tapes ({', '.join(f'{k} {v}' for k, v in sorted(counts.items()))}), {bad} failures")
    # the start rule and the run from blank tape: every family configuration the rules visit, at the predicted step
    LIMIT = 10 ** 7
    cells, pos, st = {}, 0, 'A'
    s, at, nv, k = ('D', 0, 0, 5), 136, 0, 0
    while at <= LIMIT:
        while k < at:
            t = T[(st, cells.get(pos, 0))]
            cells[pos] = t[0]; pos += t[1]; st = t[2]; k += 1
        nv += 1
        if canon(cells, pos, st) != canon(*tape(s)):
            bad += 1
            print("run differs at step", at, s)
            break
        _, s, N = rule(s)
        at += N
    print(f"run from blank: {nv} family configurations at their predicted step counts up to step {LIMIT:,} "
          f"(last {k:,}), {'ok' if not bad else 'FAILED'}")
    # a worked example: D(1, 0, 0) halts
    s, tot = ('D', 1, 0, 0), 0
    while s != 'halt':
        tot += rule(s)[2]; s = rule(s)[1]
    print("D(1, 0, 0) -> halt:", tot, "steps by the rules,", run(T, D(1, 0, 0), 1000), "by simulation")
    return bad


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
