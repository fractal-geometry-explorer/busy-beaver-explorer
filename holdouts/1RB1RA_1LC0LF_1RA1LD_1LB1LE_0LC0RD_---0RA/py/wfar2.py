"""FAR, window DFA with token phase: last K cells (far end first) + the set of possible positions in a 3-cell token
(tokens x11 read from the far end: position 0 free, positions 1 and 2 must be 1)."""
import sys
import far
from rlctl import Machine
class TSide:
    def __init__(self, K, mode):
        self.K, self.mode = K, mode
        z = ((0, 1), "#")
        self.states = [z]; self.index = {z: 0}; self.edges = set()
    def nxt(self, st, x):
        C, w = st
        if w == "#" and x == 0: return st
        w2 = (w + str(x))[-self.K:] if self.K else ""
        if self.mode == "tokfar":
            full = (w if w != "#" else "") + str(x)
            if len(full) > self.K:
                y = int(full[0])
                C2 = tuple(sorted({(p + 1) % 3 for p in C if p == 0 or y == 1})) if (C != (0, 1) or y == 1) else C
            else: C2 = C
            return (C2, full[-self.K:])
        if self.mode == "tok":
            C2 = tuple(sorted({(p + 1) % 3 for p in C if p == 0 or x == 1}))
        else:
            C2 = ((C[0] + 1) % 3,) if C != (0, 1) else (1,)
        return (C2, w2)
    def push(self, q, x):
        n = self.nxt(self.states[q], x)
        new = n not in self.index
        if new:
            self.index[n] = len(self.states); self.states.append(n)
        j = self.index[n]
        e = (j, x, q)
        if e not in self.edges:
            self.edges.add(e); new = True
        return j, new
if __name__ == "__main__":
    mt = sys.argv[1]; mir = sys.argv[2] == "R"; K = int(sys.argv[3]); mode = sys.argv[4]; steps = int(float(sys.argv[5]))
    if mir: mt = far.mirror(mt)
    side = TSide(K, mode)
    m = Machine.parse(mt)
    N = 1 << 22
    tape = bytearray(N); Ls = [0] * N
    p = N // 2; s = 0
    marks = {steps // 4, steps // 2, steps}
    for step in range(1, steps + 1):
        w, d, s2 = m.table[s][tape[p]]
        tape[p] = w
        if d == 1:
            Ls[p] = side.push(Ls[p - 1], w)[0]; p += 1
        else: p -= 1
        s = s2
        if step in marks: print(step, len(side.states), len(side.edges), flush=True)
    ok, delta, T, HALT = far.far(m, side, True)
    print("PROVED" if ok else "no proof", sys.argv[2:])
    import collections
    print("phase sets:", collections.Counter(st[0] for st in side.states))
    print([st for st in side.states if st[0] == ()][:12])
