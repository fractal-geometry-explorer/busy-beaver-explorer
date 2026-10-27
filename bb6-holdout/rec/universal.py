"""Limit process U (v -> infinity): positions alpha*N + b with N = n+2 divisible by an arbitrarily high power of 2.
Every swap/merge test is then decided by b mod 4 alone. Class v follows U until the denominators of alpha reach ~2^v."""
import sys
import symjump as S
from fractions import Fraction as Fr
def mod4_U(d):
    assert d.b.denominator == 1
    return int(d.b) % 4
S.mod4 = mod4_U
def run(R):
    w = S.P(2, 2); marks = [["G", S.P(0, 1)], ["M", w - 2]]     # alpha in units of N: w = 2N + 2
    hist = []
    for r in range(1, R + 1):
        w, marks = S.round_events(w, marks)
        hist.append((r, w, [m[:] for m in marks[1:]]))
    return hist
if __name__ == "__main__":
    R = int(sys.argv[1])
    for r, w, ms in run(R):
        right = ms[1:]                                   # ms[0] is the left halving marker N/2^(r-1)
        assert ms[0][0] == "M" and ms[0][1].a == Fr(1, 2 ** (r - 1)) and ms[0][1].b == 0, (r, ms[0])
        desc = " ".join(f"{t}({p.a.denominator.bit_length()-1},{p.b})" for t, p in right[:-1])
        end = right[-1]; assert end[0] == "M" and end[1].a == 2
        print(r, f"end=2N+{end[1].b}", desc)
