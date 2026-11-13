"""Exact accelerated simulator for 1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF.

The tape is run-length encoded.  Three kinds of moves are applied, each an exact statement about the machine:
  * shift: a state that keeps its state and direction on a symbol crosses the whole run of that symbol;
  * M j k  (lean/Counter.lean, Mstmt):  [q,k] C>0 (110)^j 0 0 R  ->  [q+j, k+2j+2] C>0 R,  k odd >= 3, q >= (k-1)/2;
  * Z a k  (lean/Counter.lean, Zstmt):  [q,k] C>0 (110)^a 0 110 0 0 R -> [q+a, k+2a+2, 3] C>0 R, same conditions;
  * runs of M 0 (lean/Counter.lean, chain): [q,k] C>0 0^(2t+1) .. -> [q, k+2t] C>0 .., when q >= (k-1)/2 + t - 1
    (Sim.chain = True; it skips the block configurations in between);
everything else is single steps.  `blocks()` reports block configurations (head in C on the 0 right of all 1s).

usage: python3 accel.py MAXSTEPS     (prints every block configuration of the run from blank tape)
"""
import sys

# transitions: (state, read) -> (write, move(+1 R / -1 L), next) ; None = halt.  States A..F = 0..5
TR = {}
for i, g in enumerate("1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF".split("_")):
    for r in (0, 1):
        s = g[3 * r:3 * r + 3]
        TR[(i, r)] = None if s[2] == "-" else (int(s[0]), 1 if s[1] == "R" else -1, ord(s[2]) - 65)
A, B, C, D, E, F = range(6)


def TM(j, m):
    return 24 * 2 ** m + 2 * j * j + 4 * m * j + 11 * j - 6


def push(st, sym, n):
    if n <= 0:
        return
    if st and st[-1][0] == sym:
        st[-1][1] += n
    else:
        st.append([sym, n])


def pop1(st):
    """remove one cell from a stack (blank beyond the end)."""
    if not st:
        return 0
    s = st[-1][0]
    st[-1][1] -= 1
    if st[-1][1] == 0:
        st.pop()
    return s


def take(st, i):
    """run i from the top (0 = nearest) as (sym, count); blank -> (0, inf)."""
    if i < len(st):
        return st[-1 - i][0], st[-1 - i][1]
    return 0, float("inf")


class Sim:
    def __init__(self):
        self.L, self.R, self.h, self.s, self.n = [], [], 0, A, 0
        self.halted = False
        self.chain = True          # apply runs of odd rounds at once (skips the block configurations between)
        self.stats = {"M": 0, "Z": 0, "shift": 0, "step": 0}

    def match_left(self):
        """left = 1^k 0 1^q ... with k odd >= 3 and q >= (k-1)/2: return (k, q) or None."""
        L = self.L
        if len(L) < 3 or L[-1][0] != 1 or L[-2] != [0, 1] or L[-3][0] != 1:
            return None
        k, q = L[-1][1], L[-3][1]
        if k % 2 == 0 or k < 3 or q < (k - 1) // 2:
            return None
        return k, q

    def match_right(self):
        """head 0, right = (110)^j then either '0 0' (M, j) or '0 110 0 0' (Z, a=j).  Returns (kind, j, i0, rest)."""
        R, i, j = self.R, 0, 0
        while True:
            s0, c0 = take(R, i)
            if s0 == 0:
                if j == 0 and c0 >= 2:
                    return ("M", 0, i)
                if j == 0 and c0 == 1:
                    # '0 110 00' with a = 0
                    s1, c1 = take(R, i + 1)
                    s2, c2 = take(R, i + 2)
                    if s1 == 1 and c1 == 2 and s2 == 0 and c2 >= 3:
                        return ("Z", 0, i)
                return None
            if s0 != 1 or c0 != 2:
                return None
            s1, c1 = take(R, i + 1)
            if s1 != 0:
                return None
            if c1 == 1:
                j += 1
                i += 2
                continue
            if c1 >= 3:
                return ("M", j + 1, i)
            if c1 == 2:
                s2, c2 = take(R, i + 2)
                s3, c3 = take(R, i + 3)
                if s2 == 1 and c2 == 2 and s3 == 0 and c3 >= 3:
                    return ("Z", j + 1, i)
            return None

    def cut_right(self, cells):
        """remove `cells` cells from the right stack."""
        R = self.R
        while cells > 0:
            if not R:
                return
            t = min(cells, R[-1][1])
            R[-1][1] -= t
            cells -= t
            if R[-1][1] == 0:
                R.pop()

    def macro(self):
        if self.s != C or self.h != 0:
            return False
        lm = self.match_left()
        if lm is None:
            return False
        rm = self.match_right()
        if rm is None:
            return False
        k, q = lm
        kind, j, _ = rm
        m = (k - 3) // 2
        L = self.L
        L.pop(); L.pop(); L.pop()
        if kind == "M" and j == 0 and self.chain:
            # a run of t odd rounds M 0 k, M 0 (k+2), ... at once (each one is M 0; lean/Counter.lean `chain`)
            s0, c0 = take(self.R, 0)
            zeros = c0 + 1                       # the head cell and the 0-run after it
            t = min((zeros - 1) // 2, q - m)     # need q >= m + t for the last round (m+t-1)+1
            if zeros == float("inf"):
                t = q - m
            t = max(t, 1)
            self.cut_right(2 * t - 1)
            push(L, 1, q); push(L, 0, 1); push(L, 1, k + 2 * t)
            self.n += 24 * (2 ** (m + t) - 2 ** m) - 6 * t
            self.stats["M"] += t
        elif kind == "M":
            # consumed: 3j cells of units, then one 0; new head is the next 0
            self.cut_right(3 * j + 1)
            push(L, 1, q + j); push(L, 0, 1); push(L, 1, k + 2 * j + 2)
            self.n += TM(j, m)
            self.stats["M"] += 1
        else:
            self.cut_right(3 * j + 1 + 3 + 1)
            push(L, 1, q + j); push(L, 0, 1); push(L, 1, k + 2 * j + 2); push(L, 0, 1); push(L, 1, 3)
            self.n += TM(j, m) + 4
            self.stats["Z"] += 1
        self.h = pop1(self.R)
        assert self.h == 0
        return True

    def step(self):
        tr = TR[(self.s, self.h)]
        if tr is None:
            self.halted = True
            return
        w, d, ns = tr
        near, far = (self.R, self.L) if d == 1 else (self.L, self.R)
        if ns == self.s:
            # shift over the run of the read symbol in direction d
            sym, cnt = take(near, 0)
            if sym == self.h and cnt != float("inf") and cnt > 0:
                near.pop()
                push(far, w, cnt + 1)
                self.h = pop1(near)
                self.n += cnt + 1
                self.stats["shift"] += 1
                return
        push(far, w, 1)
        self.h = pop1(near)
        self.s = ns
        self.n += 1
        self.stats["step"] += 1

    def blocks(self):
        bl = []
        for sym, c in self.L:
            if sym == 1:
                bl.append(c)
            elif c != 1:
                return None
        return bl


def run(maxn, every=None, quiet=False):
    sim = Sim()
    out = []
    while sim.n < maxn and not sim.halted:
        if sim.s == C and sim.h == 0 and not sim.R:
            b = sim.blocks()
            if b is not None and sim.L and sim.L[-1][0] == 1:
                out.append((sim.n, b))
                if every:
                    every(sim.n, b, sim)
        if not sim.macro():
            sim.step()
    return sim, out


if __name__ == "__main__":
    maxn = (10 ** int(sys.argv[1][2:]) if sys.argv[1].startswith("1e") else int(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 12
    def show(n, b, sim):
        print(n, b, flush=True)
    sim, out = run(maxn, show)
    print("end", sim.n, "halted" if sim.halted else "", sim.stats)
