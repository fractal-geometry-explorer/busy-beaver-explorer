"""An exact macro simulator with linear cycle jumps, in Python integers (the same algorithm as c/msim.c, which is limited
to 10^36 steps by its 128-bit counters; the two are compared in `check`).

The tape is cut into blocks of B cells on a fixed grid, run-length coded on two stacks.  The head is between two
blocks, moving in a direction; it enters the block in front with the block behind it as context, and the plain
machine runs inside these two blocks until it leaves them (a table).  If it leaves on the far side in the state it
entered and the block now behind it equals the block that was behind it before, the whole run of equal blocks in
front is crossed at once.

Jumps.  Sample points: the head turning from right to left after it has crossed at least one run at once.  If the last
four samples a period p apart have the same state and the same block values, the counts moved by the same vector d each
time, the steps of the three cycles are in arithmetic progression and each cycle took the same number m of macro
steps, and every count that moves is at least m + 4 at all four, then the cycle repeats: inside a cycle a count changes
by at most 1 per macro step apart from whole runs being moved or merged, so the tests made on counts (more than one
copy left? none left?) come out the same for all larger counts; the end of a cycle is then an affine function of the
counts and so is its step count, and an affine map that is a translation by d at two points of a line in direction d is
that translation on the whole line.  So k further cycles add k d to the counts and k s + e k (k-1) / 2 steps (s the
steps of the next cycle, e the common difference), as long as the moving counts stay at least m + 4.

usage: python3 msim.py run MAXEXP [MACHINE [B]]     to 10^MAXEXP steps or a halt; a line per power of ten
       python3 msim.py check                        against c/msim.c (with and without jumps) and the plain machine
"""
import os, subprocess, sys, tempfile, time

M = "1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD"
HERE = os.path.dirname(os.path.abspath(__file__))
HIST, MAXT = 24, 100000


class MSim:
    def __init__(self, machine, B=3, jump=True):
        self.B, self.jump = B, jump
        self.tm = []
        for row in machine.split("_"):
            self.tm.append([None if row[3 * b] == "-" else (int(row[3 * b]), 1 if row[3 * b + 1] == "R" else -1,
                                                           ord(row[3 * b + 2]) - 65) for b in (0, 1)])
        self.T = {}
        self.L, self.R = [], []          # [value, count], top = nearest the head
        self.st, self.dir, self.steps, self.msteps, self.njumps = 0, 1, 0, 0, 0
        self.hist, self.sample, self.chained, self.halted = [], False, False, False

    def tr(self, st, u, v, d):
        key = (st, u, v, d)
        r = self.T.get(key)
        if r is not None:
            return r
        B = self.B
        lo, hi = (u, v) if d > 0 else (v, u)
        cell = [(lo >> (B - 1 - i)) & 1 for i in range(B)] + [(hi >> (B - 1 - i)) & 1 for i in range(B)]
        p, k, s, nd = (B if d > 0 else B - 1), 0, st, None
        while True:
            t = self.tm[s][cell[p]]
            if t is None:
                nd, k = 0, k + 1
                break
            cell[p], mv, s = t
            p += mv
            k += 1
            if p < 0 or p >= 2 * B:
                nd = mv
                break
            if k > 10 ** 7:
                raise RuntimeError("loop inside a block")
        nlo = int("".join(map(str, cell[:B])), 2)
        nhi = int("".join(map(str, cell[B:])), 2)
        r = ((nlo, nhi) if d > 0 else (nhi, nlo)) + (nd, s, k)      # nu, nv, ndir, nst, k
        self.T[key] = r
        return r

    @staticmethod
    def push(s, v, c):
        if not s and v == 0:
            return
        if s and s[-1][0] == v:
            s[-1][1] += c
        else:
            s.append([v, c])

    def try_jump(self, lim):
        toks = self.L + self.R
        cur = (self.st, len(self.L), tuple(t[0] for t in toks), [t[1] for t in toks], self.steps, self.msteps)
        self.hist.append(cur)
        if len(self.hist) > HIST:
            self.hist.pop(0)
        if len(toks) > MAXT:
            return
        h = self.hist
        for p in range(1, 6):
            if len(h) <= 3 * p:
                break
            c0, c1, c2, c3 = h[-1], h[-1 - p], h[-1 - 2 * p], h[-1 - 3 * p]
            if any(c[:3] != c0[:3] for c in (c1, c2, c3)):
                continue
            m = c0[5] - c1[5]
            if c1[5] - c2[5] != m or c2[5] - c3[5] != m:
                continue
            s1, s0, sm = c0[4] - c1[4], c1[4] - c2[4], c2[4] - c3[4]
            e = s1 - s0
            if s0 - sm != e:
                continue
            Mn, k, good, ds = m + 4, None, True, []
            for i in range(len(toks)):
                d = c0[3][i] - c1[3][i]
                if c1[3][i] - c2[3][i] != d or c2[3][i] - c3[3][i] != d:
                    good = False
                    break
                ds.append(d)
                if d == 0:
                    continue
                if min(c[3][i] for c in (c0, c1, c2, c3)) < Mn:
                    good = False
                    break
                if d < 0:
                    kk = (c0[3][i] - Mn) // (-d)
                    k = kk if k is None or kk < k else k
            if not good or k is None or k < 2:
                continue
            sn = s1 + e
            if sn <= 0 or e < 0:
                continue
            room = lim - self.steps
            lo, hi = 0, k
            while lo < hi:
                mid = lo + (hi - lo + 1) // 2
                if mid * sn + e * (mid * (mid - 1) // 2) <= room:
                    lo = mid
                else:
                    hi = mid - 1
            k = lo
            if k < 2:
                continue
            for t, d in zip(toks, ds):
                t[1] += k * d
            self.steps += k * sn + e * (k * (k - 1) // 2)
            self.njumps += 1
            self.hist = []
            return

    def run(self, lim):
        L, R, push = self.L, self.R, self.push
        while self.steps < lim and not self.halted:
            if self.jump and self.sample:
                self.sample = self.chained = False
                self.try_jump(lim)
                if self.steps >= lim:
                    break
            d = self.dir
            f, bh = (R, L) if d > 0 else (L, R)
            v, c, u = 0, 1, 0
            if f:
                v, c = f[-1]
            if bh:
                u = bh[-1][0]
                bh[-1][1] -= 1
                if bh[-1][1] == 0:
                    bh.pop()
            nu, nv, nd, nst, k = self.tr(self.st, u, v, d)
            self.msteps += 1
            if nd == 0:
                push(bh, u, 1)
                self.steps += k
                self.halted = True
                return
            if nd == d and nst == self.st and nv == u and f and c > 1:
                f.pop()
                self.steps += k * c
                push(bh, nu, c)
                push(bh, u, 1)
                self.chained = True
            else:
                if f:
                    f[-1][1] -= 1
                    if f[-1][1] == 0:
                        f.pop()
                self.steps += k
                self.st = nst
                if nd == d:
                    push(bh, nu, 1)
                    push(bh, nv, 1)
                else:
                    push(f, nv, 1)
                    push(f, nu, 1)
                    if d > 0 and self.chained:
                        self.sample = True
                    self.dir = nd

    def tape(self, cap=10 ** 9):
        w = lambda v, c: format(v, "0%db" % self.B) + ("^%d" % c if c > 1 else "")
        left = [w(v, c) for v, c in self.L]
        right = [w(v, c) for v, c in reversed(self.R)]
        if len(left) + len(right) > cap:
            return "%d tokens" % (len(left) + len(right))
        return " ".join(left + ["%s>" % "ABCDEF"[self.st] if self.dir > 0 else "<%s" % "ABCDEF"[self.st]] + right)


def short(n):
    s = str(n)
    return s if len(s) < 30 else "%s.%se%d" % (s[0], s[1:6], len(s) - 1)


def cmd_run(maxexp, machine=M, B=3):
    a, t0 = MSim(machine, B), time.time()
    for e in range(3, maxexp + 1):
        a.run(10 ** e)
        if a.halted:
            break
        print("10^%d: %d macro steps, %d jumps, %d tokens, %.0f s" % (e, a.msteps, a.njumps, len(a.L) + len(a.R),
                                                                     time.time() - t0), flush=True)
    if a.halted:
        print("HALT after %d steps (%d macro steps, %d jumps)" % (a.steps, a.msteps, a.njumps))
        print("about %s steps; the tape at the halt:" % short(a.steps))
    else:
        print("no halt in %s steps" % short(a.steps))
    print(a.tape(400))


def cmd_check():
    d = os.path.join(tempfile.gettempdir(), "msim-25899")
    os.makedirs(d, exist_ok=True)
    for n in ("msim", "chk"):
        subprocess.run(["gcc", "-O2", "-o", os.path.join(d, n), os.path.join(HERE, "..", "c", n + ".c")], check=True)
    out = lambda *a: subprocess.run(list(a), capture_output=True, text=True).stdout.strip().split("\n")[-1]
    for c in ("12345", "1e6", "3e8", "2e9"):
        o = out(os.path.join(d, "msim"), M, "30", "3", c, "J")
        p = out(os.path.join(d, "chk"), M, o.split()[1])
        print("plain machine, %s steps:" % o.split()[1], "same state, head, ones and hash" if o == p else "DIFFERENT")
        assert o == p
    for c in ("1e13", "3e15"):
        o, p = out(os.path.join(d, "msim"), M, "30", "3", c, "J"), out(os.path.join(d, "msim"), M, "30", "3", c)
        print("jumps against no jumps, %s steps:" % o.split()[1], "same" if o == p else "DIFFERENT")
        assert o == p
    for e in (18, 36):
        o = out(os.path.join(d, "msim"), M, str(e), "3", "-1", "J")
        a = MSim(M)
        a.run(10 ** e)
        mine = "RUNNING %d msteps %d : %s" % (a.steps, a.msteps, a.tape())
        print("Python against C at 10^%d steps:" % e, "same steps, macro steps and tape" if o.strip() == mine.strip() else "DIFFERENT")
        assert o.strip() == mine.strip()


if __name__ == "__main__":
    if sys.argv[1] == "run":
        cmd_run(int(sys.argv[2]), *(sys.argv[3:4]), *(map(int, sys.argv[4:5])))
    else:
        cmd_check()
