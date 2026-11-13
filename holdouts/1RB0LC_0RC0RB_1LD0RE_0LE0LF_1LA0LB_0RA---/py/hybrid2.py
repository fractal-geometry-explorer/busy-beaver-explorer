"""hybrid.py extended to visits whose right part, or whose result, is not a plain block list (needed for
D1 = 1LF, F0 = 0LD, where an F-event leaves a gadget `0 1` between two blocks for a while).  Such a visit is still a
function of the right half of the tape, so it is simulated and memoised on the raw run-length form."""
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rle, cf, hybrid
from hybrid import FastRLE, runs_of, split_right

def freeze(R):
    return tuple((w, n) for w, n in R)

def listlike(R):
    """no spread run (a rotation of 1000 repeated) in the right part: only plain blocks and single cells"""
    for w, n in R:
        if len(w) > 1 and w != (1, 0) * (len(w) // 2):
            return False
    return True


class Hybrid2(hybrid.Hybrid):
    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self.rawmemo = {}
        self.stats.update({"raw": 0, "rawmemo": 0, "rawout": 0})

    def go(self, l, t0, depth=0):
        l = tuple(l)
        if self.use_cf and cf.clean(l):
            self.stats["cf"] += 1
            return 1, (0, 0), tuple(cf.go(l)), cf.steps(l) + 1
        if l in self.memo:
            self.stats["memo"] += 1
            st, pre, X, T, fev = self.memo[l]
            for (dt, y, ctx) in fev:
                self.fev.append((t0 + dt, y, ctx))
            return st, pre, X, T
        self.stats["sim"] += 1
        self.stats["maxdepth"] = max(self.stats.get("maxdepth", 0), depth)
        sim = FastRLE(self.m)
        sim.right = runs_of(((0,), l))
        sim.q = 0
        return self._finish(sim, t0, depth, self.memo, l)

    def _finish(self, sim, t0, depth, memo, key):
        nf = len(self.fev)
        res = self._run(sim, t0, stop_left=True, depth=depth)
        if res == "halt":
            raise rle.Halt()
        st, R = res
        pre, X = split_right(R)
        if X is None:
            self.stats["rawout"] += 1
            out = (st, None, freeze(R), sim.steps)
        else:
            out = (st, pre, tuple(X), sim.steps)
        memo[key] = out + ([(t - t0, y, c) for (t, y, c) in self.fev[nf:]],)
        return out

    def go_raw(self, key, t0, depth):
        if key in self.rawmemo:
            self.stats["rawmemo"] += 1
            st, pre, X, T, fev = self.rawmemo[key]
            for (dt, y, ctx) in fev:
                self.fev.append((t0 + dt, y, ctx))
            return st, pre, X, T
        self.stats["raw"] += 1
        self.stats["maxdepth"] = max(self.stats.get("maxdepth", 0), depth)
        sim = FastRLE(self.m)
        sim.right = [[w, n] for w, n in key]
        sim.q = 0
        return self._finish(sim, t0, depth, self.rawmemo, key)

    def _run(self, sim, t0, stop_left=False, depth=0, N=None, on_event=None):
        lastd = 0
        while True:
            if N is not None and sim.steps >= N:
                return None
            if sim.q == 0 and lastd == -1 and sim.right and sim.right[-1][0][0] == 0 and sim.pos >= (1 if stop_left else -10 ** 18):
                l = rle.suffix_list(sim)
                res = None
                if l:
                    if on_event:
                        on_event(sim, l)
                    res = self.go(l, t0 + sim.steps, depth + 1)
                elif l is None and len(sim.right) > 3 and listlike(sim.right):
                    res = self.go_raw(freeze(sim.right), t0 + sim.steps, depth + 1)
                if res is not None:
                    st, pre, X, T = res
                    c = sim.pop_left()
                    if pre is None:
                        sim.right = [[w, n] for w, n in X]
                    else:
                        sim.right = runs_of((pre, X))
                    sim.right.append([(c,), 1])
                    sim.pos -= 1
                    sim.steps += T
                    sim.q = st
                    lastd = -1
                    if stop_left and sim.pos < 0:
                        sim.pop_right()
                        return st, sim.right
                    if st == 5:
                        self.f_event(sim, t0)
                    continue
            p0, q0 = sim.pos, sim.q
            try:
                crossed = sim.try_cross()
                if not crossed:
                    sim.step()
            except rle.Halt:
                self.halted = t0 + sim.steps
                self.f_event(sim, t0, halt=True)
                return "halt"
            d = sim.pos - p0
            if d:
                lastd = 1 if d > 0 else -1
            if stop_left and sim.pos < 0:
                sim.pop_right()
                return sim.q, sim.right
            if not crossed and sim.q == 5 and q0 != 5:
                self.f_event(sim, t0)
