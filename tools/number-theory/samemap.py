"""Three holdouts iterate one function.

  f(n) = 3n - 10*2^k + 3k + 14   for h_k < n < h_(k+1),   h_k = 5*2^k - k - 6   (3, 12, 31, 70, 149, ...),
  and n = h_k (k >= 1) halts.

1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE   orbit of 4   (README: n' = 3n - 10*2^k + 3k + 14)
1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE   orbit of 10  (its round value is N = 2n + 2: N' = 3N + 24 + 6j - 20*2^j)
1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE   orbit of 1   (its thresholds c_i = 10*2^i - i - 7 are h_(i+1))

The three tables are one table started in different states (holdouts/related.json); this says more: the three
reduced maps are the same function.  The script checks the first values against each README and that the three
orbits share no value in their first STEPS terms (then they never merge before that point).

usage: python3 tools/number-theory/samemap.py [STEPS]   (default 20000, about a minute)
"""
import sys


def h(k):
    return 5 * (1 << k) - k - 6


def f(n):
    k = max(n.bit_length() - 4, 0)
    while h(k + 1) <= n:
        k += 1
    while k > 0 and h(k) >= n:
        k -= 1
    if n in (h(k), h(k + 1)):
        return None
    return 3 * n - 10 * (1 << k) + 3 * k + 14


def orbit(n, steps):
    out = []
    for _ in range(steps):
        out.append(n)
        n = f(n)
        if n is None:
            break
    return out


if __name__ == "__main__":
    steps = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    a, b, c = orbit(4, steps), orbit(10, steps), orbit(1, steps)
    assert a[:7] == [4, 9, 24, 52, 99, 163, 198]                       # P(4), P(9), ... in its README
    assert [2 * n + 2 for n in b[:5]] == [22, 56, 124, 254, 490]       # N column of its README
    assert c[:8] == [1, 7, 18, 34, 45, 78, 100, 166]                   # orbit table of its README
    sa, sb, sc = set(a), set(b), set(c)
    print(f"{len(a)}, {len(b)}, {len(c)} terms (none halts); shared values: "
          f"{len(sa & sb)}, {len(sa & sc)}, {len(sb & sc)}")
