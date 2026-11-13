"""Token-run accelerated simulator for 2-symbol TMs (exact).

Tape: two stacks of [word(tuple), count]; nearest-head entry last.  Words are written left to right.
The head sits between cells facing dir (+1 right / -1 left).  When it faces a run w^n, one copy of w is simulated
alone; if the head leaves it at the far side in the same state, the whole run is crossed at once.
"""
import sys

STATES = "ABCDEF"


def parse(m):
    t = []
    for s in m.split("_"):
        row = []
        for i in (0, 3):
            x = s[i:i + 3]
            row.append(None if x[0] == "-" else (int(x[0]), 1 if x[1] == "R" else -1, STATES.index(x[2])))
        t.append(row)
    return t


class TRun:
    def __init__(self, m, maxw=8):
        self.t = parse(m) if isinstance(m, str) else m
        self.L = []   # left stack, entries [word, count]; word left to right; top = nearest head (rightmost)
        self.R = []   # right stack; top = nearest head (leftmost)
        self.q = 0
        self.d = 1
        self.steps = 0
        self.halted = False
        self.cache = {}
        self.maxw = maxw
        self.pos = 0  # head boundary position

    # one copy of word w, entered from side d in state q
    def cross(self, q, w, d):
        key = (q, w, d)
        r = self.cache.get(key)
        if r is not None:
            return r
        c = list(w)
        k = len(c)
        i = 0 if d == 1 else k - 1
        n = 0
        seen = set()
        while 0 <= i < k:
            tr = self.t[q][c[i]]
            if tr is None or (q, i, tuple(c)) in seen:
                r = None
                break
            seen.add((q, i, tuple(c)))
            c[i], mv, q = tr
            i += mv
            n += 1
        else:
            r = (q, tuple(c), 1 if i >= k else -1, n)
        self.cache[key] = r
        return r

    def push(self, st, w, c, front_is_right):
        # st: stack to push onto; for the left stack words are appended at the right end (top)
        if st and st[-1][0] == w:
            st[-1][1] += c
            return
        st.append([w, c])
        self.compact(st, front_is_right)

    def compact(self, st, left_stack):
        # merge single-cell literals on top into runs of short words
        # gather trailing single cells (count 1, len 1)
        if len(st) < 2:
            return
        # case: top cells spell the word of the run below them
        for L in range(1, self.maxw + 1):
            if len(st) < L + 1:
                break
            tail = st[-L:]
            if not all(len(x[0]) == 1 and x[1] == 1 for x in tail):
                break
            cells = tuple(x[0][0] for x in tail)
            if not left_stack:
                cells = cells[::-1]
            below = st[-L - 1]
            if below[0] == cells:
                del st[-L:]
                below[1] += 1
                return
            if len(st) >= 2 * L:
                tail2 = st[-2 * L:-L]
                if all(len(x[0]) == 1 and x[1] == 1 for x in tail2):
                    cells2 = tuple(x[0][0] for x in tail2)
                    if not left_stack:
                        cells2 = cells2[::-1]
                    if cells2 == cells and (L == 1 or len(set(cells)) > 1):
                        # avoid words that are powers of shorter words
                        if not any(L % p == 0 and cells == cells[:p] * (L // p) for p in range(1, L)):
                            del st[-2 * L:]
                            st.append([cells, 2])
                            return

    def _deep_push(self, st, cells):
        """push literal cells (in stack order, deepest first) and merge each with the entry below if it is the same
        one-letter word"""
        for x in cells:
            if st and st[-1][0] == (x,):
                st[-1][1] += 1
            else:
                st.append([(x,), 1])

    def pop_cell(self, st, left_stack):
        """Take the cell nearest the head off stack st (blank if empty)."""
        if not st:
            return 0
        w, c = st.pop()
        if len(w) == 1:
            if c > 1:
                st.append([w, c - 1])
            return w[0]
        if left_stack:
            self._deep_push(st, w[:-1])
            if c > 1:
                st.append([w[-1:] + w[:-1], c - 1])
            return w[-1]
        self._deep_push(st, list(reversed(w[1:])))
        if c > 1:
            st.append([w[1:] + w[:1], c - 1])
        return w[0]

    def step(self):
        if self.halted:
            return False
        q, d = self.q, self.d
        front, back = (self.R, self.L) if d == 1 else (self.L, self.R)
        if front:
            w, c = front[-1]
            if len(w) > 1 or c > 1:
                for k in (1, 2, 3, 4, 6):
                    if c // k < 1 or (k > 1 and c // k < 2):
                        break
                    ww = w * k
                    r = self.cross(q, ww, d)
                    if r is not None and r[0] == q and r[2] == d:
                        n = c // k
                        front.pop()
                        if c % k:
                            front.append([w, c % k])
                        self.steps += n * r[3]
                        self.pos += d * n * len(ww)
                        y = r[1]
                        # store result in its primitive form when possible
                        for p in range(1, len(y) + 1):
                            if len(y) % p == 0 and y == y[:p] * (len(y) // p):
                                self.push(back, y[:p], n * (len(y) // p), d == 1)
                                break
                        return True
        x = self.pop_cell(front, d == -1)
        tr = self.t[q][x]
        if tr is None:
            self.halted = True
            self.push(front, (x,), 1, d == -1)
            self.steps += 1
            return False
        y, mv, q2 = tr
        self.steps += 1
        # head was facing cell x on side d; write y; move mv
        # the written cell ends up on the side opposite to the move direction
        if mv == d:
            self.push(back, (y,), 1, d == 1)
            self.pos += d
        else:
            # head turns: the cell stays in front... the head moves back across the boundary
            self.push(front, (y,), 1, d == -1)
            # now head faces the other way; it must cross nothing: head between cells, facing back
            # careful: facing cell x at boundary; writing y and moving opposite puts head on the far side?
        self.q, self.d = q2, mv
        return True

    def tape(self):
        lw = [("".join(map(str, w)), c) for w, c in self.L]
        rw = [("".join(map(str, w)), c) for w, c in reversed(self.R)]
        return lw, rw

    def cells(self):
        out = []
        for w, c in self.L:
            out.extend(w * c)
        n = len(out)
        for w, c in reversed(self.R):
            out.extend(w * c)
        return out, n


def check(m, n):
    """Compare with a plain simulator."""
    t = parse(m)
    tape = {}
    p, q = 0, 0
    r = TRun(m)
    import random
    while r.steps < n:
        if not r.step():
            break
    target = r.steps
    s = 0
    while s < target:
        x = tape.get(p, 0)
        tr = t[q][x]
        if tr is None:
            break
        tape[p], mv, q = tr
        p += mv
        s += 1
    cells, n0 = r.cells()
    hp = r.pos  # boundary; facing right means head on cell pos
    head = r.pos if r.d == 1 else r.pos - 1
    assert head == p, (head, p)
    assert q == r.q, (q, r.q)
    lo = r.pos - n0
    for i, x in enumerate(cells):
        assert tape.get(lo + i, 0) == x, (i, lo + i)
    for k, v in tape.items():
        if v and not (lo <= k < lo + len(cells)):
            raise AssertionError(("missing", k))
    return target


if __name__ == "__main__":
    m = sys.argv[1]
    for n in (10, 100, 1000, 10000, 100000, 1000000):
        print(n, check(m, n))


def head_cells(st, n, left_stack=False):
    """the n cells nearest the head on stack st, nearest first"""
    out = []
    for w, c in reversed(st):
        ww = w[::-1] if left_stack else w
        for _ in range(min(c, n)):
            out.extend(ww)
            if len(out) >= n:
                return out[:n]
    return out


def tape_str(r):
    s = []
    for w, c in r.L:
        s.append(''.join(map(str, w)) * c)
    s.append('>' if r.d == 1 else '<')
    for w, c in reversed(r.R):
        s.append(''.join(map(str, w)) * c)
    return ''.join(s)


def rle(s, words):
    """tokenize string s greedily with words {name: str}; run-length code"""
    ws = sorted(words.items(), key=lambda x: -len(x[1]))
    out = []
    i = 0
    while i < len(s):
        for nme, w in ws:
            if s.startswith(w, i):
                out.append(nme); i += len(w); break
        else:
            out.append(s[i]); i += 1
    r = []
    j = 0
    while j < len(out):
        k = j
        while k < len(out) and out[k] == out[j]:
            k += 1
        r.append(out[j] if k - j == 1 else f"{out[j]}^{k-j}")
        j = k
    return ' '.join(r)
