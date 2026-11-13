"""Exact accelerated simulator for 1RB1LC_1LC0RD_0LE1LA_---1RA_1RF0LA_0RF0RB on a run-length tape.

Three exact shortcuts read off the transition table:
  * A/C moving left over a run of 1s (A1 -> 1LC, C1 -> 1LA): the run is crossed whole, the state flips per cell;
  * F moving right over a run of 0s (F0 -> 0RF);
  * the travelling hole `A> 0 1 1 1 -> 1 A> 0 1 1` (five steps): crossed b-2 cells at once in `A> 0 1^b`.
And jumps over repeated periods: the tape is recorded each time A or E reads a 0; when four records p apart have
the same run pattern and the run lengths change by the same vector three times (step differences in arithmetic
progression), the period is repeated k times at once (k keeps every shrinking run >= MARGIN).  The jumps are
checked against the plain machine (`c/rounds.c`: the same round starts at the same step counts for 6*10^10 steps;
with the jumps switched off, BLKP=0, every E record of 3*10^7 steps), not proved.

usage: python3 accel.py STEPS (e.g. 1e9, 1e2000) [--rec] [--rounds] [--time S]
"""
import sys, time
M = "1RB1LC_1LC0RD_0LE1LA_---1RA_1RF0LA_0RF0RB"
MARGIN = 12
import os
P = int(os.environ.get("BLKP", "6"))

def parse(m):
    T = {}
    for i, g in enumerate(m.split("_")):
        for r in (0, 1):
            t = g[3*r:3*r+3]
            T[(i, r)] = None if t[2] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, "ABCDEF".index(t[2]))
    return T

class Sim:
    def __init__(self, m=M):
        self.T = parse(m)
        self.L = []   # runs [sym,count], top = nearest the head
        self.R = []   # top (end of list) = cell under the head
        self.s = 0
        self.steps = 0
        self.halted = False
        self.hist = []
        self.jumps = 0
        self.lastdir = 1

    def push(self, st, sym, c=1):
        if st and st[-1][0] == sym:
            st[-1][1] += c
        elif st or sym:
            st.append([sym, c])

    def pop(self, st):
        if not st:
            return 0
        r = st[-1]
        r[1] -= 1
        if r[1] == 0:
            st.pop()
        return r[0]

    def read(self):
        return self.R[-1][0] if self.R else 0

    def step(self):
        """One macro move. Returns False on halt."""
        L, R, s = self.L, self.R, self.s
        r = self.read()
        # travelling hole
        if s == 0 and r == 0 and len(R) >= 2 and R[-1][1] == 1 and R[-2][0] == 1 and R[-2][1] >= 3:
            k = R[-2][1] - 2
            R.pop(); R[-1][1] -= k
            self.push(L, 1, k)
            R.append([0, 1])
            self.steps += 5 * k
            self.lastdir = -1
            return True
        if (s == 0 or s == 2) and r == 1 and L and L[-1][0] == 1 and L[-1][1] >= 2:
            c = L[-1][1]
            L.pop()
            self.push(R, 1, c)
            self.steps += c
            if c & 1:
                self.s = 2 - s
            self.lastdir = -1
            return True
        if s == 5 and r == 0 and R and R[-1][1] >= 2:
            c = R[-1][1]
            R.pop()
            self.push(L, 0, c)
            self.steps += c
            self.lastdir = 1
            return True
        t = self.T[(s, r)]
        if t is None:
            self.halted = True
            return False
        w, d, ns = t
        self.pop(R)
        if d == 1:
            self.push(L, w)
        else:
            self.push(R, w)
            self.push(R, self.pop(L))
        self.s = ns
        self.steps += 1
        self.lastdir = d
        return True

    def tape(self):
        out = []
        for sym, c in self.L:
            out.append(f"{sym}^{c}" if c > 1 else str(sym))
        out.append("ABCDEF"[self.s] + ">")
        first = True
        for sym, c in reversed(self.R):
            if first and c > 1:
                out.append(str(sym)); c -= 1
            first = False
            out.append(f"{sym}^{c}" if c > 1 else str(sym))
        if not self.R:
            out.append("0")
        return " ".join(out)

    def snap(self):
        sig = (self.s, tuple(a for a, _ in self.L), tuple(a for a, _ in self.R))
        cnt = [c for _, c in self.L] + [c for _, c in self.R]
        return sig, cnt, self.steps

    def try_jump(self):
        h = self.hist
        sig, cnt, st = h[-1]
        for p in range(1, P + 1):
            if len(h) < 3 * p + 1:
                break
            a, b, c = h[-1 - p], h[-1 - 2 * p], h[-1 - 3 * p]
            if not (a[0] == sig and b[0] == sig and c[0] == sig):
                continue
            d = [x - y for x, y in zip(cnt, a[1])]
            if d != [x - y for x, y in zip(a[1], b[1])] or d != [x - y for x, y in zip(b[1], c[1])]:
                continue
            if not any(d):
                continue
            # the intermediate records must repeat with the same pattern as well
            ok = True
            for q in range(1, p):
                x, y, z = h[-1 - q], h[-1 - q - p], h[-1 - q - 2 * p]
                if not (x[0] == y[0] == z[0]):
                    ok = False; break
                dq = [u - v for u, v in zip(x[1], y[1])]
                if dq != [u - v for u, v in zip(y[1], z[1])]:
                    ok = False; break
            if not ok:
                continue
            s1, s2, s3 = st - a[2], a[2] - b[2], b[2] - c[2]
            if s1 - s2 != s2 - s3:
                continue
            k = None
            for x, dx in zip(cnt, d):
                if dx < 0:
                    kk = (x - MARGIN) // (-dx)
                    k = kk if k is None else min(k, kk)
            if k is None or k < 2:
                continue
            dd = s1 - s2
            # steps of the next k periods: s1+dd, s1+2dd, ...
            self.steps += k * s1 + dd * k * (k + 1) // 2
            n = len(self.L)
            for i, dx in enumerate(d):
                if i < n:
                    self.L[i][1] += k * dx
                else:
                    self.R[i - n][1] += k * dx
            self.hist = []
            self.jumps += 1
            return True
        return False

    def run(self, maxsteps, rec=None, tl=1e18):
        t0 = time.time()
        n = 0
        while self.steps < maxsteps:
            if self.lastdir == -1 and (self.s == 0 or self.s == 4) and self.read() == 0:
                if rec:
                    rec(self)
                self.hist.append(self.snap())
                if len(self.hist) > 3 * P + 2:
                    del self.hist[0]
                self.try_jump()
            if not self.step():
                return False
            n += 1
            if n % 2000 == 0 and time.time() - t0 > tl:
                break
        return True

if __name__ == "__main__":
    a = sys.argv[1]
    steps = 10 ** int(a[2:]) if a.startswith("1e") else int(float(a))
    tl = float(sys.argv[sys.argv.index("--time") + 1]) if "--time" in sys.argv else 1e18
    S = Sim()
    rec = None
    if "--rec" in sys.argv:
        rec = lambda S: print(S.steps, S.tape())
    if "--rounds" in sys.argv:
        def rec(S):
            if S.s == 0 and not S.L and S.R and len(S.R) >= 2 and S.R[-1] == [0, 3]:
                print(S.steps, S.tape()[:200], flush=True)
    ok = S.run(steps, rec, tl)
    print("#", "HALT" if not ok else "running", "steps", S.steps if S.steps < 10**30 else "about 10^%d" % (S.steps.bit_length() * 30103 // 100000), "jumps", S.jumps, "runs", len(S.L) + len(S.R))
    if not ok: print(S.tape()[:500])
