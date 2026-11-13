"""The macro map of this machine at the V = 0 moments, in the shape found in round 5/6, and its checks.

At a V = 0 moment the tape is `0^inf U 0 D> H (11)^n 1 0^inf` with header H = 0110101 a 1 b 1 (two flags a, b);
N is the up-counter read as one binary number (exact rebuild: ../../1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py/
rebuild.py).  One rebuild plus the tick phase after it sends (H, n, N) to (H', n', Nnew).  Observed shape:

    a = 0   "copy":  n' = n + 1,  Nnew = N + 2^(n + 1)   (N is kept and gets one more 1 on top), a' = 1, b' = b.
    a = 1   "eat":   an even number s of low digits of N is read; n' = n + 3s/2 + 1 and
                     Nnew = 2^n' + (N >> s) - delta, delta a function of the digits read (only 0 < delta < 2^(3s+8)
                     is checked here); any new flags.
            The number s is given by a walk over the digits b0, b1, ... of N (b0 lowest):
              b = 0:  b0 = 0 -> s = 2;   b0 = 1 -> state Q on the pairs (b1,b2), (b3,b4), ...
              b = 1:  b0 = 1 -> s = 2;   b0 = 0 -> state R on the pairs (b1,b2), (b3,b4), ...
              Q: (1,1) -> Q   (0,0) -> R   (0,1), (1,0) -> stop        R: (x,0) -> R   (x,1) -> stop
            stopping on the k-th pair gives s = 2k + 2 (one digit beyond the pair is read as well).

This is a description fitted to computed rebuilds, not a theorem.  `check` compares it with the exact rebuild.

usage: python3 map.py check T B     T random N of B digits, all four headers, n = B - 1, B and B + 1
       python3 map.py small B       every N with 2^(B-1) <= N < 2^B
"""
import os, sys, random, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB", "py"))
M = "1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE"
HS = ["01101010101", "01101010111", "01101011101", "01101011111"]


def walk(b, N):
    """s, the number of digits eaten with flag b, or None if the walk does not stop inside N"""
    L = N.bit_length()
    b0 = N & 1
    if b0 == b: return 2
    s = "Q" if b == 0 else "R"; k = 0
    while 2 * k + 2 < L:
        x = (N >> (2 * k + 1)) & 1; y = (N >> (2 * k + 2)) & 1; k += 1
        if s == "Q":
            if x != y: return 2 * k + 2
            s = "Q" if x else "R"
        elif y: return 2 * k + 2
    return None


def compare(rb, H, n, N):
    a, b = int(H[7]), int(H[9])
    L = N.bit_length()
    r = rb.rebuild(H, n, N, maxd=10 ** 8)
    if a == 0:
        if N & (N + 1) == 0: return "copy: N all ones, left out"
        if r[0] != "OK": return "copy: " + r[0]
        H2, n2, N2, V2, f, Lw = r[2]
        ok = n2 == n + 1 and N2 + V2 == N + (1 << (n + 1)) and H2[7] == "1" and H2[9] == H[9]
        return "copy ok" if ok else "copy CONTRADICTS"
    s = walk(b, N)
    if s is None or s > L - 3: return "eat: walk reaches the top (" + r[0] + ")"
    if r[0] != "OK": return "eat CONTRADICTS (" + r[0] + ")"
    H2, n2, N2, V2, f, Lw = r[2]
    Nn = N2 + V2
    delta = (1 << n2) + (N >> s) - Nn
    ok = n2 == n + 3 * s // 2 + 1 and 0 < delta < (1 << (3 * s + 8))
    return "eat ok" if ok else "eat CONTRADICTS"


if __name__ == "__main__":
    from rebuild import Rebuilder
    rb = Rebuilder(M); c = collections.Counter(); bad = []
    if sys.argv[1] == "check":
        random.seed(1); T, B = int(sys.argv[2]), int(sys.argv[3])
        Ns = [(1 << (B - 1)) | random.getrandbits(B - 1) for _ in range(T)]
    else:
        B = int(sys.argv[2]); Ns = range(1 << (B - 1), 1 << B)
    for N in Ns:
        for H in HS:
            for n in (B - 1, B, B + 1):
                k = compare(rb, H, n, N); c[k] += 1
                if "CONTRA" in k and len(bad) < 10: bad.append((H, n, bin(N)))
    for k, v in sorted(c.items()): print(f"{v:8d}  {k}")
    for x in bad: print("   ", x)
