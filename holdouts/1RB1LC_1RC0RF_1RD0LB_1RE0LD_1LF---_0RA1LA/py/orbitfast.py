"""1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA: the orbit of 22 under the digit map, fast and exact.

    f(10a + d) = 31a + K[d // 2],   K = [15, 27, 47, 35, 36]      (lean/DigitMap.lean: one step = one phase)

The low digits of an orbit only depend on the low digits of the start, and for m >= 1
    f(10^m A + B) = 10^(m-1) 31 A + f(B)
(lean/DigitClosed.lean, `fd_split`).  So c steps from x = 10^(c+M) H + L are 10^M 31^c H + f^c(L): the c steps run on
the (c+M)-digit number L only, and the high part H is touched once (one division, one multiplication, GMP).  Applied
recursively (halve c each time) this is the usual divide and conquer, about M(n) log n for n steps.  Along the way x_j mod 10^M is exact for every step j, which is what the end of a level reads.

usage: python3 orbitfast.py KSTEPS OUT [CHUNK] [SAMPLE]
  writes OUT.r   (one byte per step: r_k = (x_k mod 10) // 2, k = 0..KSTEPS-1, x_0 = 22)
         OUT.lo  (every SAMPLE-th step: "k x_k mod 10^20", for the end-of-level outcomes in orbitstats.py)
  and prints the number of digits of x_K and x_K mod 10^20 (and a SHA-256 of x_K's decimal string when K <= 10^6).
Checked against the plain orbit (python3 orbitfast.py --check).
"""
import sys
import gmpy2
from gmpy2 import mpz

K = [15, 27, 47, 35, 36]
M = 20


def f(x):
    return 31 * (x // 10) + K[(x % 10) // 2]


P10 = {}
P31 = {}


def p10(e):
    if e not in P10:
        P10[e] = mpz(10) ** e
    return P10[e]


def p31(e):
    if e not in P31:
        P31[e] = mpz(31) ** e
    return P31[e]


def steps(x, c, k, rs, los, sample, base=256):
    """f^c(x), appending r_k .. r_(k+c-1) to rs and (j, x_j mod 10^M) for sampled j; divide and conquer."""
    if c <= base:
        pm = p10(M)
        for j in range(c):
            d = int(x % 10)
            rs.append(d // 2)
            if (k + j) % sample == 0:
                los.append((k + j, int(x % pm)))
            x = 31 * (x // 10) + K[d // 2]
        return x
    c1 = c // 2
    H, L = gmpy2.f_divmod(x, p10(c1 + M))
    y = steps(L, c1, k, rs, los, sample, base)
    if H:
        y += H * p31(c1) * p10(M)
    return steps(y, c - c1, k + c1, rs, los, sample, base)


def run(ksteps, out=None, chunk=1 << 20, sample=100):
    x = mpz(22)
    rs = bytearray()
    los = []
    k = 0
    while k < ksteps:
        c = min(chunk, ksteps - k)
        x = steps(x, c, k, rs, los, sample)
        k += c
    return x, rs, los


def check():
    import random
    for _ in range(5):
        ks = random.randint(1, 3000)
        ch = random.randint(1, 400)
        x, rs, los = run(ks, chunk=ch, sample=7)
        y, r2 = 22, bytearray()
        lo2 = []
        for k in range(ks):
            if k % 7 == 0:
                lo2.append((k, y % 10 ** M))
            r2.append((y % 10) // 2)
            y = f(y)
        assert x == y and rs == r2 and los == lo2, (ks, ch)
    print("orbitfast = plain orbit (5 random lengths and chunk sizes)")


if __name__ == "__main__":
    if sys.argv[1] == "--check":
        check()
        sys.exit()
    ks = int(float(sys.argv[1]))
    out = sys.argv[2]
    chunk = int(sys.argv[3]) if len(sys.argv) > 3 else 1 << 20
    sample = int(sys.argv[4]) if len(sys.argv) > 4 else 100
    x, rs, los = run(ks, out, chunk, sample)
    open(out + ".r", "wb").write(bytes(rs))
    with open(out + ".lo", "w") as fh:
        for k, v in los:
            fh.write("%d %d\n" % (k, v))
    nd = gmpy2.num_digits(x, 10)  # may be one too large
    s = None
    if ks <= 10 ** 6:
        import hashlib
        t = x.digits(10)
        nd = len(t)
        s = hashlib.sha256(t.encode()).hexdigest()
    print("x_%d: about %d digits, mod 10^20 = %d%s" % (ks, nd, int(x % mpz(10) ** 20), "" if s is None else ", sha256 " + s))
