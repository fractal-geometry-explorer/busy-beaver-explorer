"""tent.py: how far the binary expansion of u = 2x/(2x + y) predicts the rules of
1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE.

    python3 py/tent.py [RULES]      # default 3,000,000

The wiki's rules (op of py/rules.py) send B(x, y) to the next tape; whether a rule doubles (x' = 2x + 2) or folds
(x' = y + O(1)) is decided by u = 2x/(2x + y) against 1/2, and up to O(1/(2x + y)) u goes to the tent map T(u)
(2u below 1/2, 2 - 2u above).  The tent map is the shift on the Gray-coded binary expansion of u, so the whole
fold/double word of T's orbit can be read off u's digits.  Here: along the real run from B(1, 0), for each tape B(x, y)
with n = 2x + y, the number of rules for which T's orbit of u (exact rationals) gives the real rules' fold/double word,
against log2(n).  The O(1/n) corrections are doubled by every later rule, so the agreement must end after about
log2(n) rules: the digits of u say nothing about the rules after that, and the digit reading cannot reach further than
running the rules themselves.
"""
import sys, os, math, collections
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rules import op


def word_real(x, y, k):
    w = []
    for _ in range(k):
        n = op(x, y)
        if n is None: break
        w.append('D' if n[0] == 2 * x + 2 else 'F')    # doubling: x' = 2x + 2 (also B(x, 2x + 2) -> B(2x + 1, 0): F)
        x, y = n
    return w


def word_tent(u, k):
    w = []
    for _ in range(k):
        if u < Fraction(1, 2): w.append('D'); u = 2 * u
        else: w.append('F'); u = 2 - 2 * u
    return w


def gray_word(u, k):
    """the same word from the binary digits of u: digit b_i XOR b_(i+1) ... (tent = shift with flips)."""
    bits = []
    v = u
    for _ in range(k + 1):
        v *= 2
        b = int(v >= 1); bits.append(b); v -= b
    # T^i(u) < 1/2 iff the (i+1)-th digit of T^i(u) is 0; T flips all later digits after a 1: digit i+1 of T^i(u) is b_(i+1) xor b_i
    w, prev = [], 0
    for i in range(k):
        w.append('D' if (bits[i] ^ prev) == 0 else 'F'); prev = bits[i]
    return w


def main():
    R = int(sys.argv[1]) if len(sys.argv) > 1 else 3000000
    x, y = 1, 0
    gap = collections.Counter()
    samples = []
    for r in range(R):
        nxt = op(x, y)
        if nxt is None: print('halt'); return
        x, y = nxt
        if y > 0 and x >= 16 and r % 997 == 0:
            n = 2 * x + y
            u = Fraction(2 * x, n)
            K = int(math.log2(n)) + 12
            wr, wt = word_real(x, y, K), word_tent(u, K)
            assert wt == gray_word(u, K)
            L = next((i for i in range(len(wr)) if wr[i] != wt[i]), len(wr))
            gap[L - int(math.log2(n))] += 1
            if len(samples) < 8 or r > R - 2000: samples.append((r, x, y, L, math.log2(n)))
    for s in samples[:8] + samples[-3:]:
        print('rule %d  B(%d, %d)  word agrees for %d rules, log2(n) = %.1f' % s)
    print('agreement length minus floor(log2 n), over %d samples:' % sum(gap.values()))
    for k in sorted(gap): print('  %+d: %d' % (k, gap[k]))


if __name__ == '__main__':
    main()
