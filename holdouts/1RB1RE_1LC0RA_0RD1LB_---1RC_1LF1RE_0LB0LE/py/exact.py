"""The rules of lean/Map.lean with exact step counts, and the map f with the steps of each case, checked against
direct simulation.

    W(p, q, r) := 0^inf (10)^p 0 (10)^q 1^r E> 0^inf
    X(p, q)    := 0^inf (10)^p 0 (10)^q A> 0^inf

usage: python3 py/exact.py          # every rule on a grid of tapes, and the run from blank tape
"""
import re
import sys

TM = "1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE"

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


def W(p, q, r):
    return cfg('10' * p + '0' + '10' * q + '1' * r, 'E', '')


def X(p, q):
    return cfg('10' * p + '0' + '10' * q, 'A', '')


def tape(s):
    return W(*s[1:]) if s[0] == 'W' else X(*s[1:])


def rule(s):
    """The rules w1 ... w6 of lean/Map.lean: (name, next configuration or 'halt', steps)."""
    if s[0] == 'X':
        _, p, q = s
        if p >= 1:
            return 'w3', ('W', p, 0, 2 * q + 2), 4 * (q - 2) + 18
        return 'w4', ('W', 2, 0, 2 * q + 1), 12 * (q - 2) + 51
    _, p, q, r = s
    if r >= 2:
        if p >= 1:
            return 'w1', ('W', p - 1, q + 2, r - 1), 4 * q + 4 * (r - 2) + 13
        return 'w5', ('W', q + 2, 0, r - 1), 4 * q + 4 * (r - 2) + 17
    if p >= 1:
        return 'w2', ('X', p - 1, q + 2), 4 * q + 9
    return 'w6', 'halt', 4 * q + 13                     # 4q + 12 steps to D on a 0, then the halting step


def f(p, r):
    """The map f of lean/Map.lean on the samples W(p, 0, r), with the number of machine steps of each case."""
    if r >= p + 2:
        return 'double', (2 * p + 2, r - p - 1), 2 * p * p + 4 * p * r + 7 * p + 4 * r + 9
    if r == p + 1:
        return 'halt', 'halt', 6 * p * p + 15 * p + 13
    if r == p:
        return 'r = p', (2, 4 * p + 1), 6 * p * p + 27 * p + 27
    return 'reset', (p - r, 4 * r + 2), 6 * r * r + 11 * r + 10


def shape(cells, pos, st):
    """('W', p, q, r) or ('X', p, q) if the configuration has that form, else None."""
    if st not in 'EA' or any(v for i, v in cells.items() if i >= pos):
        return None
    lo = min([i for i, v in cells.items() if v] + [pos])
    w = ''.join(str(cells.get(i, 0)) for i in range(lo, pos))
    left, right = (w.split('00', 1) if '00' in w else ('', w))
    if '00' in w:
        left += '0'
    if not re.fullmatch(r'(10)*', left):
        return None
    x = re.fullmatch(r'((?:10)*)(1*)', right)
    if not x:
        return None
    p, q, r = len(left) // 2, len(x.group(1)) // 2, len(x.group(2))
    if st == 'E':
        return ('W', p, q, r) if r >= 1 else None
    return ('X', p, q) if r == 0 else None


def first(T, c, n, samples_only=False):
    """Steps from c to the first W or X configuration (or sample W(p, 0, r)), or to the halt, at most n steps."""
    cells, pos, st = dict(c[0]), c[1], c[2]
    hi = max([i for i, v in cells.items() if v] + [-1])
    for k in range(1, n + 1):
        t = T[(st, cells.get(pos, 0))]
        if t is None:
            return 'halt', k
        cells[pos] = t[0]
        if t[0]:
            hi = max(hi, pos)
        elif pos == hi:
            while hi >= 0 and not cells.get(hi, 0):
                hi -= 1
        pos += t[1]; st = t[2]
        if pos > hi and st in 'EA':
            s = shape(cells, pos, st)
            if s and (not samples_only or (s[0] == 'W' and s[2] == 0)):
                return s, k
    return '?', n


def main():
    T = table(TM)
    bad = n = 0
    counts = {}

    def check(name, got, want, count=True):
        nonlocal bad, n
        if count:
            n += 1
            counts[name] = counts.get(name, 0) + 1
        if got != want:
            bad += 1
            print("differs:", name, got, want)

    for p in range(0, 20):
        for q in range(0, 20):
            for r in range(1, 12):
                name, t, N = rule(('W', p, q, r))
                check(name, first(T, W(p, q, r), N), (t, N))
            if q >= 2:
                name, t, N = rule(('X', p, q))
                if name == 'w4':    # passes W(0, 0, 2q + 2) after 4q + 10 steps (w3 with p = 0), then one w5
                    check(name, first(T, X(p, q), N), (('W', 0, 0, 2 * q + 2), 4 * q + 10))
                    r_, c_ = run(T, X(p, q), N)
                    check(name, canon(*c_), canon(*tape(t)), False)
                else:
                    check(name, first(T, X(p, q), N), (t, N))
    for p in range(0, 40):
        for r in range(1, 80):
            name, t, N = f(p, r)
            if name == 'r = p':     # passes the sample W(0, 0, 4p + 2) after 6p^2 + 11p + 10 steps (a reset)
                check('f: ' + name, first(T, W(p, 0, r), N, True), (('W', 0, 0, 4 * p + 2), 6 * p * p + 11 * p + 10))
                r_, c_ = run(T, W(p, 0, r), N)
                check('f: ' + name, canon(*c_), canon(*W(t[0], 0, t[1])), False)
            else:
                check('f: ' + name, first(T, W(p, 0, r), N, True), (t if t == 'halt' else ('W', t[0], 0, t[1]), N))
    print(f"grid: {n} tapes, each run to its next W or X configuration (rules w1-w6) or next sample W(p, 0, r) "
          f"(map f), or to the halt")
    for k, v in sorted(counts.items()):
        print(f"    {k}: {v}")
    print(f"    failures: {bad}")
    # the run from blank tape: every W and X configuration at its predicted step, and no others
    LIMIT = 10 ** 7
    cells, pos, st = {}, 0, 'A'
    s, at, k, nv, ns, runbad, hi = ('W', 2, 0, 1), 27, 0, 0, 0, 0, -1
    cur = None
    while at <= LIMIT and not runbad:
        while k < at:
            t = T[(st, cells.get(pos, 0))]
            cells[pos] = t[0]
            if t[0]:
                hi = max(hi, pos)
            elif pos == hi:
                while not cells.get(hi, 0):
                    hi -= 1
            pos += t[1]; st = t[2]; k += 1
            if 27 < k < at and pos > hi and st in 'EA':
                f_ = shape(cells, pos, st)
                if f_ and not (cur[0] == 'X' and cur[1] == 0 and f_ == ('W', 0, 0, 2 * cur[2] + 2)):
                    runbad = 1
                    print("run: a configuration the rules skip, at step", k, f_)
        nv += 1
        if canon(cells, pos, st) != canon(*tape(s)):
            runbad = 1
            print("run differs at step", at, s)
            break
        if s[0] == 'W' and s[2] == 0:
            ns += 1
        cur = s
        _, s, N = rule(s)
        at += N
    print(f"run from blank: all {nv} W and X configurations up to step {LIMIT:,} come at the predicted steps "
          f"({ns} of them samples W(p, 0, r)), and no others: {'ok' if not runbad else 'FAILED'}")
    # the samples of the run: the map f with its step counts
    x, t, out = (2, 1), 27, []
    while t <= LIMIT:
        out.append((t, x))
        name, x, N = f(*x)
        t += N
    print("    samples by f:", ", ".join(f"W{(a, 0, b)} at {u:,}" for u, (a, b) in out[:6]), "...",
          f"({len(out)} up to step {LIMIT:,}, as above: {len(out) == ns})")
    for s in [(1, 4)]:
        tot, cur, path = 0, s, []
        while cur != 'halt':
            name, cur, N = f(*cur)
            tot += N; path.append(N)
        print(f"W({s[0]}, 0, {s[1]}) -> halt: {' + '.join(map(str, path))} = {tot} steps by f,",
              run(T, W(s[0], 0, s[1]), 10 ** 6), "by simulation")
    return bad + runbad + (len(out) != ns)


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
