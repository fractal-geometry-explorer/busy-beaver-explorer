"""The rule table with exact step counts (lean/Macro.lean, lean/Reduction.lean), checked against direct simulation.

    K(p, q) := 0^inf A> 0 1^p 0 1^q 0^inf

usage: python3 py/exact.py          # every rule on a grid of tapes, and the run from blank tape
"""
import sys

TM = "1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE"

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


def K(p, q):
    return cfg('', 'A', '0' + '1' * p + '0' + '1' * q)


def rule(p, q):
    """(name, next (p, q) or 'halt', steps): the cases of F and T in lean/Reduction.lean, halting step included."""
    if p == 0:
        return 'K_zero', (2, q - 1), 7
    if p == 1:
        return 'K_one_halts', 'halt', 7     # 6 steps to F on a 0, then the halting step
    if p % 2 == 1:
        k = (p - 3) // 2
        return 'K_odd', (k, q + k + 4), 2 * k * k + 10 * k + 13
    k = (p - 2) // 2
    return 'K_even', (3 * k + 3 + q, 1), q * (4 * k + 8) + 6 * k * k + 22 * k + 15


def main():
    T = table(TM)
    bad = n = 0
    counts = {}
    for p in range(0, 61):
        for q in range(1 if p == 0 else 0, 41):
            name, t, N = rule(p, q)
            r, c = run(T, K(p, q), N)
            ok = (r == 'halt' and c == N) if t == 'halt' else (r == 'ok' and canon(*c) == canon(*K(*t)))
            n += 1
            counts[name] = counts.get(name, 0) + 1
            if not ok:
                bad += 1
                print("differs:", (p, q), name, t, N, r)
    print(f"grid: {n} tapes ({', '.join(f'{k} {v}' for k, v in sorted(counts.items()))}), {bad} failures")
    LIMIT = 10 ** 8
    cells, pos, st = {}, 0, 'A'
    s, at, nv, k = (0, 2), 7, 0, 0
    while at <= LIMIT:
        while k < at:
            t = T[(st, cells.get(pos, 0))]
            cells[pos] = t[0]; pos += t[1]; st = t[2]; k += 1
        nv += 1
        if canon(cells, pos, st) != canon(*K(*s)):
            bad += 1
            print("run differs at step", at, s)
            break
        _, s, N = rule(*s)
        at += N
    print(f"run from blank: {nv} samples K(p, q) at their predicted step counts up to step {LIMIT:,} "
          f"(the last at step {k:,}),{'ok' if not bad else 'FAILED'}")
    s, tot = (13, 0), 0
    while s != 'halt':
        tot += rule(*s)[2]; s = rule(*s)[1]
    print("K(13, 0) -> halt:", tot, "steps by the rules,", run(T, K(13, 0), 10 ** 5), "by simulation")
    return bad


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
