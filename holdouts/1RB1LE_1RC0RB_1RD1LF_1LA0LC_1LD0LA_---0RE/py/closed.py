"""The macro map of 1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE in closed form, its checks and a fast macro run.

Macro state at a V = 0 moment: (a, b, n, N), header 0110101 a 1 b 1, N the up-counter, n the digits of V (map.py).

    a = 0  "copy":  (1, b, n + 1, N + 2^(n+1))                                    (N not all ones)
    a = 1  "eat":   (a', b', n', 2^n' + (N >> s) - delta),  n' = n + 3s/2 + 1,    (s, a', b', delta) = eat(b, N)

`eat` reads the digits b0, b1, ... of N.  If b0 = b: s = 2, delta = 27 - b1 (b = 0) or 11 (b = 1), a' = b0,
b' = b0 xor b1.  Otherwise it walks over the pairs (x, y) = (b1, b2), (b3, b4), ..., in mode Q if b = 0 and in mode R
if b = 1, collecting terms; k counts the pairs skipped since the last term:

    Q:  (1,1) skip      (0,0) term 2^(5k+9) - 48 8^k - 10, go to R
        (0,1) stop, last term (2^(2k+3) - 1) 2^(3k+6) + 2^(3k+4) + 1
        (1,0) stop, last term (2^(2k+4) - 1) 2^(3k+6) + 2^(3k+4) + 1 - e
    R:  (0,0) skip      (1,0) term 2^(5k+4) + 78 8^k - 10, stay in R
        (0,1) stop, last term 2^(5k+5) + 78 8^k + 1 - e
        (1,1) stop, last term 2^(5k+4) + 78 8^k + 1

e is the digit after the stopping pair (it is read too: s = 2 (pairs) + 2).  delta is the sum of the terms, each
shifted left by 3 cells per pair read after it.  a' = y in Q and x in R; b' = a' xor e.  So b is a borrow pending on
the counter, and R is Q with a borrow pending.  The formulas were fitted to the exact rebuild and checked against it
(`check`, `blank`); they are not proved.

usage: python3 closed.py check B        every class of low digits with s <= B, b = 0 and 1, against the exact rebuild
       python3 closed.py blank K        the first K rebuilds from blank tape: exact macro run against the map
       python3 closed.py run T [SECONDS]  T steps of the map from blank tape (fast), statistics of s
"""
import os, sys, time, collections
from array import array
HERE = os.path.dirname(os.path.abspath(__file__))
M = "1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE"
FAM = os.path.join(HERE, "..", "..", "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB", "py")
OUT = 10 ** 9


def eat(b, N):
    """(s, a', b', delta), or (OUT, 0, 0, 0) if the walk does not stop within the digits of N"""
    if (N & 1) == b:
        b1 = (N >> 1) & 1
        return 2, N & 1, (N & 1) ^ b1, (27 - b1) if b == 0 else 11
    mode = b; i = 0; k = 0; terms = []; U = N >> 1
    while True:
        if U < 8: return OUT, 0, 0, 0
        p = U & 3; U >>= 2; i += 1        # bit 0 of p is x, the lower digit
        if mode == 0:
            if p == 3: k += 1; continue
            if p == 0: terms.append(((1 << (5 * k + 9)) - (48 << (3 * k)) - 10, i)); mode = 1; k = 0; continue
            e = U & 1; a2 = p >> 1
            if p == 2: T = (((1 << (2 * k + 3)) - 1) << (3 * k + 6)) + (1 << (3 * k + 4)) + 1
            else: T = (((1 << (2 * k + 4)) - 1) << (3 * k + 6)) + (1 << (3 * k + 4)) + 1 - e
        else:
            if p == 0: k += 1; continue
            if p == 1: terms.append(((1 << (5 * k + 4)) + (78 << (3 * k)) - 10, i)); k = 0; continue
            e = U & 1; a2 = p & 1
            if p == 2: T = (1 << (5 * k + 5)) + (78 << (3 * k)) + 1 - e
            else: T = (1 << (5 * k + 4)) + (78 << (3 * k)) + 1
        return 2 * i + 2, a2, a2 ^ e, T + sum(c << (3 * (i - ii)) for c, ii in terms)


def step(a, b, n, N):
    """the next macro state, or None where the map is not defined (copy of an all-ones counter, walk at the top)"""
    if a == 0:
        if N & (N + 1) == 0: return None
        return 1, b, n + 1, N + (1 << (n + 1))
    s, a2, b2, d = eat(b, N)
    if s > N.bit_length() - 3: return None
    n2 = n + 3 * s // 2 + 1
    return a2, b2, n2, (1 << n2) + (N >> s) - d


def exact_states(K):
    """macro states (a, b, n, N) after rebuilds 0 .. K - 1 of the exact macro run from blank tape"""
    sys.path.insert(0, FAM)
    from rebuild import macro_run
    out = []
    macro_run(M, K, 1e9, lambda x: out.append((int(x[1][7]), int(x[1][9]), x[2], x[3])) if isinstance(x[0], int) else None)
    return out


def fast_run(a, b, n, N, T, tmax=1e18):
    low = N; tp = n; q = array("H"); qh = 0; big = {}
    hist = collections.Counter(); mx = 0; recs = []; ratio = 0.0; t0 = time.time(); t = 0; copies = 0
    def pull():
        nonlocal qh, tp, low
        if qh >= len(q): return False
        g = q[qh]; g = big.pop(qh) if g == 0 else g
        qh += 1; tp += g; low |= 1 << tp
        return True
    for t in range(T):
        if a == 0:
            g = 1; n += 1; a = 1; copies += 1      # a new 1 directly above the top
        else:
            while True:
                s, a2, b2, d = eat(b, low)
                if low.bit_length() >= s + d.bit_length() + 4: break
                if not pull(): return "top", t, n, hist, recs, copies
            n2 = n + 3 * s // 2 + 1
            low = (low >> s) - d; tp -= s; g = n2 - (n - s); n = n2; a, b = a2, b2
            hist[s] += 1
            if s > mx: mx = s; recs.append(("longest", t + 1, s, n))
            if t > 1000 and s > ratio * n: ratio = s / n; recs.append(("ratio", t + 1, s, n))
        if g < 65536: q.append(g)
        else: big[len(q)] = g; q.append(0)
        if t & 0xfff == 0:
            if qh > (1 << 24):
                big = {i - qh: v for i, v in big.items()}; q = q[qh:]; qh = 0
            if time.time() - t0 > tmax: break
    return "ok", t + 1, n, hist, recs, copies


def main():
    cmd = sys.argv[1]
    if cmd == "check":
        sys.path.insert(0, FAM)
        from rebuild import Rebuilder
        rb = Rebuilder(M); B = int(sys.argv[2]); bad = 0; tot = 0
        for b in (0, 1):
            H = "0110101" + "1" + "1" + str(b) + "1"; seen = set()
            for low in range(1 << B):
                s, a2, b2, d = eat(b, low | (1 << (B + 4)))
                if s > B or (s, low & ((1 << s) - 1)) in seen: continue
                seen.add((s, low & ((1 << s) - 1)))
                N = (0b1001 << (4 * B + 8)) | low
                for n in (N.bit_length() - 1, N.bit_length()):
                    r = rb.rebuild(H, n, N, maxd=10 ** 9)
                    ok = r[0] == "OK"
                    if ok:
                        H2, n2, N2, V2, f, Lw = r[2]
                        ok = (int(H2[7]), int(H2[9]), n2, N2 + V2) == step(1, b, n, N)
                    if not ok: bad += 1; print("differs:", b, n, bin(N))
            tot += len(seen)
        print(f"{tot} classes of low digits with s <= {B} (b = 0 and 1), two values of n each: {bad} differ from the exact rebuild")
        sys.exit(1 if bad else 0)
    if cmd == "blank":
        K = int(sys.argv[2]); st = exact_states(K); bad = 0; kinds = collections.Counter()
        for i in range(K - 1):
            kinds["copy" if st[i][0] == 0 else "eat"] += 1
            if step(*st[i]) != st[i + 1]: bad += 1; print("differs after rebuild", i, st[i][:3])
        print(f"{K - 1} macro steps from blank tape ({dict(kinds)}): {bad} differ from the exact macro run; n = {st[-1][2]}")
        print("first macro state:", st[0])
        sys.exit(1 if bad else 0)
    if cmd == "run":
        T = int(sys.argv[2]); tmax = float(sys.argv[3]) if len(sys.argv) > 3 else 1e18
        st0 = exact_states(1)[0]; t0 = time.time(); pre = min(T, 2000)
        for i in range(pre):           # the first steps with the whole counter as one number
            st0 = step(*st0)
            if st0 is None: print("the map is not defined at macro step", i); sys.exit(1)
        st, t, n, hist, recs, copies = fast_run(*st0, T - pre, tmax)
        print(f"{st}: {pre} + {t} macro steps (of the {t}: {copies} copies, {t - copies} eats), V has {n} digits, "
              f"{time.time() - t0:.0f} s")
        for x in (2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536):
            print(f"  s >= {x}: {sum(v for j, v in hist.items() if j >= x)}")
        print("records (kind, macro step, s, n):")
        for r in recs: print("  ", r)


if __name__ == "__main__":
    main()
