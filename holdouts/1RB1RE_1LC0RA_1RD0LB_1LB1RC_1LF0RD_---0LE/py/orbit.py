"""The map of 1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE on n, read at the samples S(n) = `C> 0 (10)^n 1` (the head
at the left end of the tape).

Thresholds c_i = 10*2^i - i - 7 (i >= -1): -1, 3, 12, 31, 70, 149, 308, ...  For c_i < n < c_{i+1}:

    phase 1:  S(n) -> T(x, z) = C> 0 (10)^x 111 0 (10)^z 1   with x = 2(n - c_i - 1), z = c_{i+1} - n - 3
    phase 2:  T(x, z) -> S(2x + z + 4)
    together: n -> 3n - 2c_i + i + 3  =  3n - 20*2^i + 3i + 17

and n = c_i halts (in phase 1).  The next value is c_{i+1}, a halt, exactly when 3n = 4c_i + 3, which needs
c_i = 0 mod 3, i.e. i = 0 or 1 mod 6.

`ph` below is the map exactly as Lean defines it (lean/Phase1.lean, `next n = ph (n - 1) 0 0`), one bounce at a
time; `python3 orbit.py cmp N` checks that it equals the closed form f for 1 <= n < N.

usage: python3 orbit.py STEPS [REPORT_EVERY]       iterate from n = 1 (the first sample, step 4)
       python3 orbit.py check SAMPLES_FILE         compare with the samples printed by c/samples.c
"""
import sys


def c(i):
    return (10 << i if i >= 0 else 5) - i - 7


def level(n):
    """The i with c_i < n <= c_{i+1}."""
    i = max(-1, n.bit_length() - 5)
    while c(i + 1) < n:
        i += 1
    while c(i) >= n:
        i -= 1
    return i


def f(n):
    """The next sample, or None for a halt."""
    i = level(n)
    if n == c(i + 1):
        return None
    return 3 * n - 2 * c(i) + i + 3


def ph(K, i, m):
    """The Lean definition of the first phase (and the second after it): the next sample, None for a halt."""
    while True:
        if m == 0:
            if K < 4:
                return [4 * i + 7, 4 * i + 10, None, 2 * i + 9][K]
            K, i, m = K - 4, 0, 2 * i + 5
        else:
            if K == 0:
                return 4 * i + m + 7
            K, i, m = K - 1, i + 1, m - 1


def cmp(N):
    bad = [n for n in range(1, N) if ph(n - 1, 0, 0) != f(n)]
    print('ph(n-1, 0, 0) == f(n) for 1 <= n <', N, ':', not bad, bad[:5])


def run(steps, every):
    n = 1
    closest = None
    for k in range(1, steps + 1):
        i = level(n)
        ci = c(i)
        if ci % 3 == 0:  # a halt is possible at the next step: how far is n from (4c_i + 3)/3 ?
            d = abs(3 * n - 4 * ci - 3) / ci
            if ci > 10 ** 6 and (closest is None or d < closest[0]):
                closest = (d, k, ci.bit_length())
        m = f(n)
        if m is None:
            print('HALT at map step', k, 'n =', n)
            return
        n = m
        if k % every == 0:
            print(k, 'bits', n.bit_length(), 'level', level(n), 'closest', closest, flush=True)
    print('done', steps, 'bits', n.bit_length(), 'closest', closest)


def check(path):
    obs = [int(l.split()[1]) for l in open(path) if l.split()[0].isdigit() and len(l.split()) == 2]
    n, pred = 1, []
    for _ in obs:
        pred.append(n)
        n = f(n)
    print(len(obs), 'samples', obs[:8], '; equal to the orbit of 1:', pred == obs)


if __name__ == '__main__':
    if sys.argv[1] == 'cmp':
        cmp(int(sys.argv[2]))
    elif sys.argv[1] == 'check':
        check(sys.argv[2])
    else:
        run(int(sys.argv[1]), int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 5)
