"""Fast exact runs of "affine residue walks": one big number x and a small counter p, where each step is

    x -> (A*x + B[r]) / D,   p -> p + DELTA[r],   r = x mod D   (gcd(A, D) = 1)

except at "special" steps, which can only happen when the counter p (before the step) is <= LOW. Special steps are
done with the map module's own exact `step` (so halts, resets and floors are exactly the Lean map).

The residues of K consecutive steps depend only on x mod D^K, and K steps together are an affine map
x -> (A^K x + C) / D^K. A divide and conquer over K (leaves of L steps from a table over residues mod D^L)
computes C, the counter's total change and its prefix minimum for K steps in O(M(K) log K) time, from x mod D^K
alone. If the counter cannot reach LOW inside the block, the whole block is applied at once; otherwise the block is
done one step at a time with the module's `step`. Every block's result is checked to divide exactly.

Specs (state layout of the module, A, D, B, DELTA, LOW):
    m_1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_ZZZ0RA  (Antihydra)   (p, a):      A=3 D=2 B=(4,5)    DELTA=(-1,+2)
    m_1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_ZZZ1RA               ("r", n, m): A=3 D=2 B=(4,7)    DELTA=(+2,-1)
    m_1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_ZZZ0RC               (m, k):      A=4 D=3 B=(12,8,7) DELTA=(-1,+1,+1)

usage:
    python3 tools/sweep/residue.py check SLUG N          # compare with the module's step for N steps
    python3 tools/sweep/residue.py run SLUG STEPS CKPT [BLOCK_LOG2]
"""
import json
import os
import sys
import time

import gmpy2
from gmpy2 import mpz

sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import engine  # noqa: E402

SPECS = {
    "m_1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_ZZZ0RA": dict(A=3, D=2, B=(4, 5), DELTA=(-1, 2), LOW=0,
                                                       get=lambda s: (s[1], s[0]), put=lambda x, p, s: (p, x)),
    "m_1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_ZZZ1RA": dict(A=3, D=2, B=(4, 7), DELTA=(2, -1), LOW=0,
                                                       get=lambda s: (s[1], s[2]) if s[0] == "r" else None,
                                                       put=lambda x, p, s: ("r", x, p)),
    "m_1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_ZZZ0RC": dict(A=4, D=3, B=(12, 8, 7), DELTA=(-1, 1, 1), LOW=0,
                                                       get=lambda s: (s[0], s[1]), put=lambda x, p, s: (x, p)),
}


class Walk:
    def __init__(self, spec):
        self.A, self.D, self.B, self.DL = spec["A"], spec["D"], spec["B"], spec["DELTA"]
        self.L = 16 if self.D == 2 else 10
        self.pw = {}
        n = self.D ** self.L
        self.leaf = []
        A, D, B, DL, L = self.A, self.D, self.B, self.DL, self.L
        AL = A ** L
        for y in range(n):  # C, total change, minimum of the counter change before each step
            x, s, mn = y, 0, 0
            for _ in range(L):
                mn = min(mn, s)
                r = x % D
                x = (A * x + B[r]) // D
                s += DL[r]
            self.leaf.append((mpz(D ** L * x - AL * y), s, mn))

    def apow(self, k):
        v = self.pw.get(k)
        if v is None:
            v = (mpz(self.A) ** k, mpz(self.D) ** k)
            self.pw[k] = v
        return v

    def block(self, y, K):
        """y = x mod D^K, K a multiple of L -> (C, total change, min of counter before each step)."""
        if K == self.L:
            return self.leaf[int(y)]
        K1 = (K // self.L // 2) * self.L
        K2 = K - K1
        A1, D1 = self.apow(K1)
        A2, D2 = self.apow(K2)
        C1, s1, m1 = self.block(y % D1, K1)
        num = A1 * y + C1
        y2 = (num // D1) % D2
        C2, s2, m2 = self.block(y2, K2)
        return A2 * C1 + D1 * C2, s1 + s2, min(m1, s1 + m2)


def run(slug, steps, ckpt=None, blog2=20, check=False):
    m = engine.load(slug)
    spec = SPECS[slug]
    W = Walk(spec)
    K = max(W.L, (2 ** blog2 // W.L) * W.L)
    AK, DK = W.apow(K)
    st = {"slug": slug, "n": 0, "state": engine.enc(m.START), "result": "running", "seconds": 0.0, "blocks": 0,
          "slow": 0}
    if ckpt and os.path.exists(ckpt):
        with open(ckpt) as f:
            st = json.load(f)
    s = engine.dec(st["state"])
    n, t0, base = st["n"], time.time(), st["seconds"]
    tl = t0
    result = "running"

    def save():
        st.update(n=n, state=engine.enc(s), result=result, seconds=base + time.time() - t0)
        if ckpt:
            with open(ckpt + ".tmp", "w") as f:
                json.dump(st, f)
            os.replace(ckpt + ".tmp", ckpt)

    while n < steps:
        g = spec["get"](s)
        if g is not None:
            x, p = g
            C, ds, mn = W.block(x % DK, K)
            if p + mn > spec["LOW"]:
                num = AK * x + C
                q, r = gmpy2.f_divmod(num, DK)
                assert r == 0
                s = spec["put"](q, p + ds, s)
                n += K
                st["blocks"] += 1
                if check:
                    return s
            else:
                g = None
        if g is None:  # slow path: K exact steps of the module
            for _ in range(K):
                s2, lab = m.step(s)
                n += 1
                st["slow"] += 1
                if s2 is None:
                    result = "HALT"
                    save()
                    print(f"{slug}: HALT at step {n}", flush=True)
                    return st
                s = s2
                g2 = spec["get"](s)
                if g2 is not None and g2[1] > spec["LOW"] + K * 2:
                    break
        now = time.time()
        if now - tl > 1800:
            tl = now
            save()
            print(f"{slug}: n={n} bits={engine.bits(s)} blocks={st['blocks']} slow={st['slow']} "
                  f"{base + now - t0:.0f}s", flush=True)
    save()
    print(f"{slug}: {result} n={n} bits={engine.bits(s)} counter={spec['get'](s)[1] if spec['get'](s) else s} "
          f"{base + time.time() - t0:.0f}s", flush=True)
    return st


def check(slug, N):
    """Fast blocks of every size from the module's states along the orbit, against plain steps."""
    m = engine.load(slug)
    spec = SPECS[slug]
    W = Walk(spec)
    s = engine.to_mpz(m.START)
    ok = 0
    for i in range(N):
        g = spec["get"](s)
        if g is not None and i % 7 == 0:
            for K in (W.L, 2 * W.L, 5 * W.L, 13 * W.L):
                x, p = g
                AK, DK = W.apow(K)
                C, ds, mn = W.block(x % DK, K)
                t, good, low = s, True, p
                for _ in range(K):
                    gg = spec["get"](t)
                    if gg is None or gg[1] <= spec["LOW"]:
                        good = False
                        break
                    low = min(low, gg[1])
                    t, _ = m.step(t)
                if not good:
                    continue
                q = (AK * x + C) // DK
                assert (AK * x + C) % DK == 0
                assert spec["get"](t) == (q, p + ds), (i, K)
                assert low == p + mn, (i, K)
                ok += 1
        s2, _ = m.step(s)
        if s2 is None:
            break
        s = s2
    print(f"{slug}: {ok} block checks ok")


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[0] == "check":
        check(a[1], int(a[2]))
    else:
        run(a[1], int(float(a[2])), a[3] if len(a) > 3 else None, int(a[4]) if len(a) > 4 else 20)
