"""The rebuild of 1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC--- as a closed integer map, its checks and a fast macro run.

Macro state at a V = 0 moment with header 0110101: (n, N), N the up-counter with its sentinel, n the number of digits
of V (see walk.py and ../../1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py/rebuild.py).  As long as the walk of walk.py
stops below the top of N, the next macro state is

    (n + c,  2^(n + c) + (N >> j) - delta),      c = (5 j + 1) / 2,     (j, delta) = W(N)

with W given by a recursion on N alone (`W` below; checked against the exact rebuild, not proved):

    N even:                                   j = 1,       delta = 4
    N = ... 1 0 (11)^k 1   (pair (1,0)):      j = 2k + 3,  delta = 1 + 2^(5k+5) (2^(2k+4) - 1)
    N = ... 0 1 (11)^k 1   (pair (0,1)):      j = 2k + 3,  delta = 4 + 2^(5k+5) (2^(2k+3) - 1)
    N = ... 0 0 (11)^k 1   (pair (0,0)):      let (j2, delta2) = W((N >> (2k + 2)) - 1) and c2 = (5 j2 + 1) / 2;
                                              j = j2 + 2k + 2,  delta = delta2 + (2^(2k+3) - 1) 2^(c2 + 2 + 5k)

(the digits are written top first, so `(11)^k 1` are the lowest 2k + 1 digits).  In the third case the rest of the
counter is decremented before the walk goes on: the states Q and R of walk.py are "no borrow" and "borrow pending".

usage: python3 map.py check B            W against the exact rebuild for every class of low digits with j <= B
       python3 map.py random T B         T random counters of B digits against the exact rebuild
       python3 map.py blank K            the first K rebuilds from blank tape: exact rebuild against the map
       python3 map.py run T [SECONDS]    T rebuilds of the map from blank tape (fast), with the statistics of j
"""
import os, sys, time, random, collections
from array import array
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "..", "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB", "py"))
M = "1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---"
H0 = "0110101"
OUT = 10 ** 9            # W's answer when the digits given run out before the walk stops
START = (28, 268311340)  # the macro state after the first rebuild from blank tape (`blank` recomputes it)


def W(U):
    """(j, delta) of the rebuild at counter U, or (OUT, 0) if the walk does not stop within the digits of U"""
    if U & 1 == 0: return 1, 4
    k = 0
    while (U >> (2 * k + 1)) & 3 == 3: k += 1
    p = (U >> (2 * k + 1)) & 3          # bit 0 is the lower digit of the pair
    if p == 1: return 2 * k + 3, 1 + (((1 << (2 * k + 4)) - 1) << (5 * k + 5))
    if p == 2: return 2 * k + 3, 4 + (((1 << (2 * k + 3)) - 1) << (5 * k + 5))
    if (U >> (2 * k + 2)) == 0: return OUT, 0
    j2, d2 = W((U >> (2 * k + 2)) - 1)
    if j2 >= OUT: return OUT, 0
    c2 = (5 * j2 + 1) // 2
    return j2 + 2 * k + 2, d2 + (((1 << (2 * k + 3)) - 1) << (c2 + 2 + 5 * k))


def step(n, N):
    """the next macro state and j, or None if the walk reaches the top two digits of N"""
    j, d = W(N)
    if j > N.bit_length() - 2: return None
    c = (5 * j + 1) // 2
    return n + c, (1 << (n + c)) + (N >> j) - d, j


def exact(rb, n, N):
    r = rb.rebuild(H0, n, N, maxd=10 ** 9)
    if r[0] != "OK": return None
    H2, n2, N2, V2, f2, L2 = r[2]
    return H2, n2, N2, (1 << n2) - V2


def check_one(rb, n, N):
    j, d = W(N)
    c = (5 * j + 1) // 2
    return exact(rb, n, N) == (H0, n + c, N >> j, d)


def fast_run(n, N, T, tmax=1e18):
    """T steps of `step` with N kept as a low part plus a queue of gaps between the isolated ones above it.
    Returns (status, steps done, n, histogram of j, records)."""
    low = N; tp = n; q = array("H"); qh = 0; big = {}
    hist = collections.Counter(); mx = 0; recs = []; ratio = 0.0; t0 = time.time(); t = 0
    for t in range(T):
        while True:
            j, d = W(low)
            if low.bit_length() >= j + d.bit_length() + 3: break
            if qh >= len(q): return "top", t, n, hist, recs
            g = q[qh]; g = big.pop(qh) if g == 0 else g
            qh += 1; tp += g; low |= 1 << tp
        c = (5 * j + 1) // 2
        low = (low >> j) - d; tp -= j
        g = c + j
        if g < 65536: q.append(g)
        else: big[len(q)] = g; q.append(0)
        n += c; hist[j] += 1
        if j > mx: mx = j; recs.append(("longest", t + 1, j, n))
        if t > 1000 and j > ratio * n: ratio = j / n; recs.append(("ratio", t + 1, j, n))
        if t & 0xfffff == 0:
            if qh > (1 << 24):
                big = {i - qh: v for i, v in big.items()}; q = q[qh:]; qh = 0
            if time.time() - t0 > tmax: break
    return "ok", t + 1, n, hist, recs


def main():
    cmd = sys.argv[1]
    if cmd in ("check", "random", "blank"):
        from rebuild import Rebuilder, first_state
        rb = Rebuilder(M)
    if cmd == "check":
        B = int(sys.argv[2]); seen = set(); bad = 0
        for low in range(1 << B):
            N = (0b1001 << (4 * B + 8)) | low
            j, d = W(low | (1 << (B + 3)))
            if j > B or (j, low & ((1 << j) - 1)) in seen: continue
            seen.add((j, low & ((1 << j) - 1)))
            for n in (N.bit_length() - 1, N.bit_length()):
                if not check_one(rb, n, N): bad += 1; print("differs:", n, bin(N))
        print(f"{len(seen)} classes of low digits with j <= {B}, two values of n each: {bad} differ from the exact rebuild")
        sys.exit(1 if bad else 0)
    if cmd == "random":
        T, B = int(sys.argv[2]), int(sys.argv[3]); random.seed(2); bad = 0; done = 0; jm = 0
        while done < T:
            N = (1 << (B - 1)) | random.getrandbits(B - 1)
            j, d = W(N)
            if j + d.bit_length() + 3 > B: continue
            done += 1; jm = max(jm, j)
            if not check_one(rb, B - 1, N): bad += 1; print("differs:", bin(N))
        print(f"{T} random counters of {B} digits (longest j = {jm}): {bad} differ from the exact rebuild")
        sys.exit(1 if bad else 0)
    if cmd == "blank":
        K = int(sys.argv[2])
        H, n, N, form, steps = first_state(M, rb)
        r = rb.rebuild(H, n, N, form); H2, n2, N2, V2, f2, L2 = r[2]
        n, N = n2, N2 + V2
        print("macro state after the first rebuild from blank tape:", (n, N), "as START:", (n, N) == START)
        bad = 0
        for i in range(K):
            e = exact(rb, n, N); s = step(n, N)
            if e is None or s is None or (e[1], e[2] + (1 << e[1]) - e[3]) != s[:2]: bad += 1; print("differs at", i)
            n, N = s[0], s[1]
        print(f"{K} rebuilds from blank tape: {bad} differ from the exact rebuild; n = {n}")
        sys.exit(1 if bad else 0)
    if cmd == "run":
        T = int(sys.argv[2]); tmax = float(sys.argv[3]) if len(sys.argv) > 3 else 1e18
        t0 = time.time()
        st, t, n, hist, recs = fast_run(START[0], START[1], T, tmax)
        print(f"{st}: {t} rebuilds after the first, V has {n} digits, {time.time() - t0:.0f} s")
        tot = sum(hist.values())
        print("j mod 4 = 3:", sum(v for j, v in hist.items() if j % 4 == 3), "of", tot)
        for x in (1, 3, 5, 9, 17, 33, 65, 129, 257, 513, 1025, 2049, 4097):
            print(f"  j >= {x}: {sum(v for j, v in hist.items() if j >= x)}")
        print("records (kind, rebuild, j, n):")
        for r in recs: print("  ", r)


if __name__ == "__main__":
    main()
