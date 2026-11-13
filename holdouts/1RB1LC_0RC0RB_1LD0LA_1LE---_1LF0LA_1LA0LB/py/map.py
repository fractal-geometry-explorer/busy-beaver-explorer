"""The rebuild of 1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB as a closed integer map, its checks and a fast macro run.

Macro state at a V = 0 moment: (h, n, N), h = 0 for header 0110101 and 1 for 0110111, N the up-counter with its
sentinel, n the number of digits of V (rebuild.py).  As long as the walk stops below the top of N the next state is

    (b,  n + c,  2^(n + c) + (N >> j) - delta),      c = (5 j + 1) / 2,     (j, b, delta) = walk(h, N).

`walk` reads N in pairs of digits from the bottom, in one of two modes, O (start for h = 0) and Q (start for h = 1).
A pair is written (upper digit, lower digit).  In both modes pairs 11 are skipped and counted (k of them); then

    O, pair 01:   stop.  b = the next digit, j = number of digits read, last term 1 - b + 2^(5k+5) (3 2^(2k+3) - 1)
    O, pair 00:   term (3 2^(2k+2) - 1) 2^(5k+5);  subtract 1 from the rest of the counter;  stay in O
    O, pair 10:   the same term;  go to Q
    Q, pair 00:   term A;       subtract 1 from the rest;  stay in Q
    Q, pair 10:   term A + 10;  subtract 1 from the rest;  go to O
    Q, pair 01:   term B;       subtract 1 from the rest;  go to O
                  A = 2^(7k+9) - 3 2^(5k+6),  B = 2^(7k+10) - 3 2^(5k+6) - 2;  directly after a Q-00 step instead
                  A = 2^(7k+10) - 2^(5k+7),   B = 2^(7k+11) - 2^(5k+7) - 2

and delta is the sum of the terms, each shifted left by 5 cells per pair read after it.  "Subtract 1 from the rest"
is what the states P and R of rebuild_rule.py stand for (O and Q with a borrow pending).  The terms were fitted to
the exact rebuild and checked against it (`check`, `random`, `blank`); none of this is proved.

usage: python3 map.py check B            every class of low digits with j <= B, both headers, against the exact rebuild
       python3 map.py random T B         T random counters of B digits, both headers
       python3 map.py blank K            rebuilds 7 .. K from blank tape: exact rebuild against the map
       python3 map.py run T [SECONDS]    T rebuilds of the map (fast) from the state after rebuild 7, statistics of j
"""
import os, sys, time, random, collections
from array import array
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
M = "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB"
HDR = ["0110101", "0110111"]
OUT = 10 ** 9
K0 = 7        # the map is used from the state after rebuild K0 on (rebuild 5 reads the counter up to its top)


def walk(h, U):
    """(j, b, delta), or (OUT, 0, 0) if the walk does not stop within the digits of U.  The subtraction of 1 from
    the rest is carried as a borrow: a pair 00 read with a borrow pending counts as 11 and keeps the borrow, any
    other pair is lowered by one and ends it."""
    s = bin(U)[:1:-1]; L = len(s)          # digits, lowest first
    S = h; i = 0; k = 0; flag = False; terms = []; borrow = False
    while True:
        if L - 2 * i < 3: return OUT, 0, 0
        p = (s[2 * i] == "1") + 2 * (s[2 * i + 1] == "1"); i += 1
        if borrow:
            if p == 0: p = 3
            else: p -= 1; borrow = False
        if p == 3: k += 1; continue
        if S == 0:
            if p == 1:
                b = int(s[2 * i])
                d = 1 - b + (((3 << (2 * k + 3)) - 1) << (5 * k + 5))
                for c, ii in terms: d += c << (5 * (i - ii))
                return 2 * i + 1, b, d
            terms.append((((3 << (2 * k + 2)) - 1) << (5 * k + 5), i)); k = 0
            if p == 0: borrow = True
            else: S = 1; flag = False
        else:
            if flag: A = (1 << (7 * k + 10)) - (1 << (5 * k + 7)); B = (1 << (7 * k + 11)) - (1 << (5 * k + 7)) - 2
            else: A = (1 << (7 * k + 9)) - (3 << (5 * k + 6)); B = (1 << (7 * k + 10)) - (3 << (5 * k + 6)) - 2
            terms.append((A if p == 0 else A + 10 if p == 2 else B, i)); k = 0; borrow = True
            if p == 0: flag = True
            else: S = 0


def step(h, n, N):
    """the next macro state and j, or None if the walk reaches the top two digits of N"""
    j, b, d = walk(h, N)
    if j > N.bit_length() - 2 or (N >> j) < 2: return None
    c = (5 * j + 1) // 2
    return b, n + c, (1 << (n + c)) + (N >> j) - d, j


def exact(rb, h, n, N):
    r = rb.rebuild(HDR[h], n, N, maxd=10 ** 9)
    if r[0] != "OK": return None
    H2, n2, N2, V2, f2, L2 = r[2]
    return HDR.index(H2), n2, N2, (1 << n2) - V2


def check_one(rb, h, n, N):
    j, b, d = walk(h, N)
    return exact(rb, h, n, N) == (b, n + (5 * j + 1) // 2, N >> j, d)


def state_after(K):
    """the exact macro states (h, n, N) after rebuilds 0 .. K from blank tape"""
    from rebuild import macro_run
    out = []
    macro_run(M, K + 1, 1e9, lambda x: out.append((HDR.index(x[1]), x[2], x[3])) if isinstance(x[0], int) else None)
    return out


def fast_run(h, n, N, T, tmax=1e18, progress=False):
    """T steps of `step`, N kept as a low part plus the gaps between the ones above it.  Returns (status, steps
    done, n, histogram of j, records, headers, state, (u, r)); status "top": the walk reaches the top two digits of
    the counter, the case the map does not cover; state is then (h, n, N).  u counts the rebuilds whose delta is
    larger than the whole unread part N >> j, r is the largest length of delta divided by the length of N >> j
    after the first 1000 rebuilds (a halt needs delta = (N >> j) + 1, so r = 1)."""
    low = N; tp = n; q = array("H"); qh = 0; big = {}
    hist = collections.Counter(); mx = 0; recs = []; ratio = 0.0; t0 = time.time(); t = 0; hb = [0, 0]; under = 0; dmax = 0.0

    def pull():
        nonlocal qh, tp, low
        g = q[qh]; g = big.pop(qh) if g == 0 else g
        qh += 1; tp += g; low += 1 << tp

    for t in range(T):
        while True:
            j, b, d = walk(h, low)
            if j <= low.bit_length() - 2: break
            if qh >= len(q): return "top", t, n, hist, recs, hb, (h, n, low), (under, dmax)
            want = 2 * low.bit_length() + 64
            while qh < len(q) and low.bit_length() < want: pull()
        c = (5 * j + 1) // 2
        if t > 1000: dmax = max(dmax, d.bit_length() / (n - j))
        low = (low >> j) - d; tp -= j; h = b; hb[b] += 1
        g = c + j
        if g < 65536: q.append(g)
        else: big[len(q)] = g; q.append(0)
        if low < 0:
            under += qh >= len(q) - 1          # delta exceeds the whole unread part: the new top digit is used up
            while low < 0: pull()
        n += c; hist[j] += 1
        if j > mx:
            mx = j; recs.append(("longest", t + 1, j, n))
            if progress: print("  longest walk so far:", t + 1, j, n, f"{time.time() - t0:.0f} s", flush=True)
        if t > 1000 and j > ratio * n:
            ratio = j / n; recs.append(("ratio", t + 1, j, n))
            if progress: print("  largest share of the counter so far:", t + 1, j, n, f"{j / n:.4f}", flush=True)
        if t & 0xff == 0:
            if qh > (1 << 24):
                big = {i - qh: v for i, v in big.items()}; q = q[qh:]; qh = 0
            if time.time() - t0 > tmax: break
    return "ok", t + 1, n, hist, recs, hb, None, (under, dmax)


def main():
    cmd = sys.argv[1]
    if cmd in ("check", "random"):
        from rebuild import Rebuilder
        rb = Rebuilder(M)
    if cmd == "check":
        B = int(sys.argv[2]); bad = 0; tot = 0
        for h in (0, 1):
            seen = set()
            for low in range(1 << B):
                j, b, d = walk(h, low | (1 << (B + 3)))
                if j > B or (j, low & ((1 << j) - 1)) in seen: continue
                seen.add((j, low & ((1 << j) - 1)))
                N = (0b1001 << (4 * B + 8)) | low
                for n in (N.bit_length() - 1, N.bit_length()):
                    if not check_one(rb, h, n, N): bad += 1; print("differs:", h, n, bin(N))
            tot += len(seen)
        print(f"{tot} classes of low digits with j <= {B} (both headers), two values of n each: {bad} differ from the exact rebuild")
        sys.exit(1 if bad else 0)
    if cmd == "random":
        T, B = int(sys.argv[2]), int(sys.argv[3]); random.seed(3); bad = 0; done = 0; jm = 0
        while done < T:
            N = (1 << (B - 1)) | random.getrandbits(B - 1); h = random.getrandbits(1)
            j, b, d = walk(h, N)
            if j + d.bit_length() + 3 > B: continue
            done += 1; jm = max(jm, j)
            if not check_one(rb, h, B - 1, N): bad += 1; print("differs:", h, bin(N))
        print(f"{T} random counters of {B} digits (longest j = {jm}): {bad} differ from the exact rebuild")
        sys.exit(1 if bad else 0)
    if cmd == "blank":
        K = int(sys.argv[2]); st = state_after(K); bad = 0
        for i in range(K0, K):
            s = step(*st[i])
            if s is None or s[:3] != st[i + 1]: bad += 1; print("differs at rebuild", i + 1)
        print(f"rebuilds {K0 + 1} .. {K} from blank tape: {bad} differ from the exact rebuild; n = {st[K][1]}")
        print("state after rebuild", K0, ":", st[K0][:2], hex(st[K0][2]))
        sys.exit(1 if bad else 0)
    if cmd == "run":
        T = int(sys.argv[2]); tmax = float(sys.argv[3]) if len(sys.argv) > 3 else 1e18
        h, n, N = state_after(K0)[K0]
        t0 = time.time()
        st, t, n, hist, recs, hb, last, under = fast_run(h, n, N, T, tmax)
        print(f"{st}: {t} rebuilds after rebuild {K0}, V has {n} digits, {time.time() - t0:.0f} s; "
              f"new header 0110101 {hb[0]} times, 0110111 {hb[1]} times")
        print(f"  rebuilds with delta > N >> j: {under[0]};  longest delta / length of N >> j after 1000 rebuilds: {under[1]:.4f}")
        for x in (3, 5, 9, 17, 33, 65, 129, 257, 513, 1025, 2049, 4097, 8193, 16385, 32769, 65537, 131073):
            print(f"  j >= {x}: {sum(v for j, v in hist.items() if j >= x)}")
        print("records (kind, rebuild after K0, j, n):")
        for r in recs: print("  ", r)


if __name__ == "__main__":
    main()
