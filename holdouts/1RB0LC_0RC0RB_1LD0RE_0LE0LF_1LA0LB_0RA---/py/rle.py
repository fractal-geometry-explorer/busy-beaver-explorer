"""An exact run-length simulator with shift rules, for the block-list family of BB(6) holdouts.

The tape is two stacks of runs (word, count): `left` (nearest the head last, each word in left-to-right order)
and `right` (nearest the head last, each word in left-to-right order); the head reads the first cell of the
right part.  A move is either one machine step or a *shift*: the head faces a run (w)^n and one copy of w,
crossed with a short literal word u carried next to the head, brings the head back to the same state with u
in front of it again; then all n copies are crossed at once (the same lemma as `TM.cross_r` / `TM.cross_l`
in tools/lean/TM/Basic.lean).  Literal cells pushed on a stack are folded back into runs of the words in
WORDS (all rotations of 10 and 1000), so the sweeps of these machines cross whole blocks in one move.

Exact: `tests` compares it cell for cell with the plain simulator.  Step counts are bbchallenge's (a halting
transition counts as a step).
"""
import sys

WORDS = [(1, 0), (0, 1), (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]


def parse(m):
    t = []
    for g in m.split("_"):
        row = []
        for y in (0, 1):
            s = g[3 * y:3 * y + 3]
            row.append(None if s[2] == "-" else (int(s[0]), 1 if s[1] == "R" else -1, ord(s[2]) - 65))
        t.append(row)
    return t


class Halt(Exception):
    pass


class RLE:
    MAXU = 3

    def __init__(self, machine):
        self.T = parse(machine)
        self.left = []          # runs [word, n]
        self.right = []
        self.q = 0
        self.steps = 0
        self.pos = 0            # head position (cells), start 0
        self.cache = {}
        self.halted = None
        self.enter = [0] * 8

    # ---------------------------------------------------------------- cells
    def pop_right(self):
        r = self.right
        if not r:
            return 0
        w, n = r[-1]
        c = w[0]
        if len(w) == 1:
            if n == 1:
                r.pop()
            else:
                r[-1][1] = n - 1
        else:
            if n == 1:
                r.pop()
            else:
                r[-1][1] = n - 1
            for x in reversed(w[1:]):
                r.append([(x,), 1])
        return c

    def pop_left(self):
        l = self.left
        if not l:
            return 0
        w, n = l[-1]
        c = w[-1]
        if n == 1:
            l.pop()
        else:
            l[-1][1] = n - 1
        if len(w) > 1:
            for x in w[:-1]:
                l.append([(x,), 1])
        return c

    def push_left(self, c):
        l = self.left
        l.append([(c,), 1])
        self._fold(l, True)

    def push_right(self, c):
        r = self.right
        r.append([(c,), 1])
        self._fold(r, False)

    def _fold(self, st, isleft):
        # fold trailing literal cells into a run of a word: on the left the literals are the last entries, read
        # left to right; on the right the literals nearest the head are last, read right to left
        for w in WORDS:
            L = len(w)
            if len(st) < L:
                continue
            tail = st[-L:]
            if not all(len(t[0]) == 1 and t[1] == 1 for t in tail):
                continue
            cells = tuple(t[0][0] for t in tail) if isleft else tuple(t[0][0] for t in reversed(tail))
            if cells != w:
                continue
            below = st[-L - 1] if len(st) > L else None
            if below is not None and below[0] == w:
                del st[-L:]
                below[1] += 1
                return
            # start a run only when the word repeats twice in literals
            if len(st) >= 2 * L:
                t2 = st[-2 * L:-L]
                if all(len(t[0]) == 1 and t[1] == 1 for t in t2):
                    c2 = tuple(t[0][0] for t in t2) if isleft else tuple(t[0][0] for t in reversed(t2))
                    if c2 == w:
                        del st[-2 * L:]
                        st.append([w, 2])
                        return

    # ---------------------------------------------------------------- shift rules
    def _sim_copy(self, q, cells, i, lo, hi):
        """run on a finite list of cells from index i in state q while lo<=i<=hi; returns (q, cells, i, n) or None"""
        n = 0
        seen = set()
        while lo <= i <= hi:
            tr = self.T[q][cells[i]]
            if tr is None:
                return None
            key = (q, i, tuple(cells))
            if key in seen:
                return None
            seen.add(key)
            cells[i], d, q = tr
            i += d
            n += 1
            if n > 400:
                return None
        return q, cells, i, n

    def _cross_right(self, q, u, w):
        key = ("r", q, u, w)
        if key in self.cache:
            return self.cache[key]
        cells = list(u) + list(w)
        res = None
        r = self._sim_copy(q, cells, len(u), 0, len(cells) - 1)
        if r is not None:
            q2, c2, i, n = r
            if q2 == q and i == len(cells) and tuple(c2[len(w):]) == u:
                res = (tuple(c2[:len(w)]), n)
        self.cache[key] = res
        return res

    def _cross_left(self, q, u, w):
        """L w q> u R  ->  L q> u v R : the head on the first cell of u, in state q, before and after"""
        key = ("l", q, u, w)
        if key in self.cache:
            return self.cache[key]
        cells = list(w) + list(u)
        i, qq, n, res = len(w), q, 0, None
        seen = set()
        while 0 <= i < len(cells) and n <= 400:
            tr = self.T[qq][cells[i]]
            if tr is None:
                break
            k2 = (qq, i, tuple(cells))
            if k2 in seen:
                break
            seen.add(k2)
            cells[i], d, qq = tr
            i += d
            n += 1
            if i == 0 and qq == q and tuple(cells[:len(u)]) == u:
                res = (tuple(cells[len(u):]), n)
                break
        self.cache[key] = res
        return res

    def try_cross(self):
        q = self.q
        # right: the head faces a run on the right; u = literal cells just left of the head (0..MAXU)
        r = self.right
        if r and len(r[-1][0]) > 1 and r[-1][1] >= 1:
            w, n = r[-1]
            l = self.left
            for j in range(0, self.MAXU + 1):
                if j > len(l):
                    break
                if j and not all(len(t[0]) == 1 and t[1] == 1 for t in l[-j:]):
                    break
                u = tuple(t[0][0] for t in l[-j:]) if j else ()
                res = self._cross_right(q, u, w)
                if res:
                    v, s = res
                    r.pop()
                    lits = l[-j:] if j else []
                    if j:
                        del l[-j:]
                    if l and l[-1][0] == v:
                        l[-1][1] += n
                    else:
                        l.append([v, n])
                    l.extend(lits)
                    self.steps += s * n
                    self.pos += len(w) * n
                    return True
        l = self.left
        if l and len(l[-1][0]) > 1:
            w, n = l[-1]
            r = self.right
            for j in range(1, self.MAXU + 1):
                if j > len(r):
                    # blank on the right counts as zeros
                    break
                if not all(len(t[0]) == 1 and t[1] == 1 for t in r[-j:]):
                    break
                u = tuple(t[0][0] for t in reversed(r[-j:]))
                res = self._cross_left(q, u, w)
                if res:
                    v, s = res
                    l.pop()
                    lits = r[-j:]
                    del r[-j:]
                    if r and r[-1][0] == v:
                        r[-1][1] += n
                    else:
                        r.append([v, n])
                    r.extend(lits)
                    self.steps += s * n
                    self.pos -= len(w) * n
                    return True
        return False

    def step(self):
        c = self.pop_right()
        tr = self.T[self.q][c]
        if tr is None:
            self.push_right(c)
            self.steps += 1
            self.halted = (self.q, c)
            raise Halt()
        w, d, q = tr
        if d == 1:
            self.push_left(w)
        else:
            self.push_right(w)
            c2 = self.pop_left()
            self.push_right(c2)
        self.pos += d
        if q != self.q:
            self.enter[q] += 1
        self.q = q
        self.steps += 1

    def move(self):
        if not self.try_cross():
            self.step()

    # ---------------------------------------------------------------- views
    def cells(self):
        L = []
        for w, n in self.left:
            L.extend(list(w) * n)
        R = []
        for w, n in reversed(self.right):
            R.extend(list(w) * n)
        return L, R


def check(machine, n):
    """compare with the plain simulator after every move for n moves"""
    from itertools import count
    T = parse(machine)
    sim = RLE(machine)
    tape = {}
    pos = 0
    q = 0
    t = 0
    for _ in range(n):
        try:
            sim.move()
        except Halt:
            pass
        while t < sim.steps:
            y = tape.get(pos, 0)
            tr = T[q][y]
            if tr is None:
                t += 1
                break
            tape[pos], d, q = tr
            pos += d
            t += 1
        L, R = sim.cells()
        assert q == sim.q and pos == sim.pos, (t, q, sim.q, pos, sim.pos)
        for i, c in enumerate(reversed(L)):
            assert tape.get(pos - 1 - i, 0) == c
        for i, c in enumerate(R):
            assert tape.get(pos + i, 0) == c
        if sim.halted:
            break
    return sim.steps


if __name__ == "__main__":
    m = sys.argv[1]
    if sys.argv[2] == "check":
        print("ok", check(m, int(sys.argv[3])))
    else:
        s = RLE(m)
        N = float(sys.argv[2])
        mv = 0
        try:
            while s.steps < N:
                s.move()
                mv += 1
        except Halt:
            print("HALT", s.steps, s.halted)
        print(s.steps, mv, len(s.left), len(s.right))


def near(sim, k=24):
    """the k cells left of the head and the k cells from the head on, as strings"""
    L = []
    for w, n in reversed(sim.left):
        for _ in range(min(n, k)):
            L.extend(reversed(w))
            if len(L) >= k:
                break
        if len(L) >= k:
            break
    R = []
    for w, n in reversed(sim.right):
        for _ in range(min(n, k)):
            R.extend(w)
            if len(R) >= k:
                break
        if len(R) >= k:
            break
    return "".join(map(str, reversed(L[:k]))), "".join(map(str, R[:k]))


def watch(machine, N, state):
    """run to N steps; print every entry into `state` (a letter) with the cells around the head"""
    sim = RLE(machine)
    s = ord(state) - 65
    while sim.steps < N:
        try:
            if not sim.try_cross():
                q0 = sim.q
                sim.step()
                if sim.q == s and q0 != s:
                    l, r = near(sim)
                    print(sim.steps, l, "[%s]" % state, r, flush=True)
        except Halt:
            print("HALT", sim.steps, sim.halted, flush=True)
            return sim
    return sim


def from_list(machine, blocks, state="A"):
    """the configuration  0^inf S> 0 (10)^b1 1 (10)^b2 1 ... (10)^bk 1 0^inf  (b as printed at a left-end event)"""
    sim = RLE(machine)
    sim.q = ord(state) - 65
    runs = [[(0,), 1]]
    for b in blocks:
        if b:
            runs.append([(1, 0), b])
        runs.append([(1,), 1])
    sim.right = list(reversed(runs))
    return sim


def suffix_list(sim):
    """if the right part (from the head) is 0 (10)^b1 1 ... (10)^bk 1 0^inf, the list [b1..bk], else None"""
    toks = list(reversed(sim.right))
    cells = []
    out = []
    # expand lazily: words other than 10/1/0 make it fail
    i = 0
    if not toks:
        return None
    # head cell must be 0
    seq = []
    for w, n in toks:
        if len(w) % 2 == 0 and w == (1, 0) * (len(w) // 2):
            seq.append(((1, 0), n * len(w) // 2))
        elif len(w) <= 4:
            seq.append((w, n))
        else:
            return None
    # flatten small runs, keep (1,0) runs as counts
    flat = []
    for w, n in seq:
        if w == (1, 0):
            flat.append(("a", n))
        elif n > 64:
            return None
        else:
            for _ in range(n):
                flat.extend([("c", x) for x in w])
    # parse
    if not flat or flat[0] != ("c", 0):
        return None
    j = 1
    while j < len(flat):
        cnt = 0
        while j < len(flat):
            if flat[j][0] == "a":
                cnt += flat[j][1]
                j += 1
            elif flat[j] == ("c", 1) and j + 1 < len(flat) and flat[j + 1] == ("c", 0) and j + 2 < len(flat) and (flat[j + 2] == ("c", 1) or flat[j + 2][0] == "a"):
                cnt += 1
                j += 2
            else:
                break
        if j >= len(flat) or flat[j] != ("c", 1):
            return None
        out.append(cnt)
        j += 1
        if all(f == ("c", 0) for f in flat[j:]):
            return out
    return out


def next_left_event(sim, maxsteps=float("inf")):
    """run until the head is back at the left end of the visited tape (pos <= 0) in state A reading 0 after a move
    left; return the suffix list there (None if the shape is different), or 'halt'"""
    start = sim.steps
    lastd = 0
    lo = 0
    while sim.steps - start < maxsteps:
        p0 = sim.pos
        try:
            if not sim.try_cross():
                sim.step()
        except Halt:
            return "halt"
        d = sim.pos - p0
        if sim.pos < lo:
            lo = sim.pos
        if d < 0:
            lastd = -1
        elif d > 0:
            lastd = 1
        if sim.q == 0 and lastd == -1 and sim.pos <= lo + 0:
            r = sim.right
            c = r[-1][0][0] if r else 0
            if c == 0:
                return suffix_list(sim)
    return None
