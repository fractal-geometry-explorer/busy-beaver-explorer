"""The run as a map on block lists: an exact simulator that does every *visit* to a list of plain blocks at once.

A *visit* (`Go`) starts when the head, in state A after a move left, reads the 0 in front of a plain right part
    A>  0 (10)^b1 1 (10)^b2 1 ... (10)^bk 1 0^inf          (frame A)
and ends when the head first steps left of that cell.  It never reads the tape on the left, so its outcome depends
on the list l = [b1..bk] only:  the exit state kappa, a short prefix w and the new list X, with
    kappa>  a | w (10)^x1 1 ... 0^inf
(a = the cell left of the start).  Four exits occur: B with w = 00 (the normal one), C with w = 0, A with w = '' and
F with w = 0 (an *F-event*: F now reads a; a = 1 is the halt).

* A **clean** visit (`cf.clean`: b1 odd >= 7, the other blocks even, b_i >= 2 + 18*5^(i-2) for the middle ones,
  last >= 2; or a single odd block) is done in closed form: exit B/00, X = l + (-5, -18, -90, ..., +12*5^(k-2))
  ((+1) for k = 1), in `cf.steps` steps.  This is the depth-m round rule, proved in Lean for every depth
  (`go_spec` in lean/Family.lean, with `clean`/`go`/`goT` the recursive form of the same thing; `cf.py` is its
  closed form, checked against the recursion).
* Any other visit is simulated with the exact run-length simulator (`rle.py`), and every visit that starts inside
  it (to the right of its start) is done recursively the same way.  Results of unclean visits are memoised.

The top level (the left end of the tape) is simulated the same way.  Everything is exact: the visits are
deterministic functions of l, and the closed form is a theorem.  `check` compares the left-end events and the
F-events with plain/run-length simulation.

usage: python3 hybrid.py MACHINE STEPS [OUT.json]
"""
import sys, os, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rle, frames, cf  # noqa: E402

sys.setrecursionlimit(100000)

PRE = {1: (0, 0), 2: (0,), 0: (), 5: (0,)}     # exit state (frame A index) -> prefix w


def runs_of(cells_then_list):
    """right stack (nearest last) for a literal prefix followed by enc(l)"""
    pre, l = cells_then_list
    runs = []
    for b in l:
        if b:
            runs.append([(1, 0), b])
        runs.append([(1,), 1])
    runs.reverse()
    for c in reversed(pre):
        runs.append([(c,), 1])
    return runs


class FastRLE(rle.RLE):
    """rle.RLE with one more shift rule: B crosses (1010)^n (six steps each, leaving (0100)^n), so a sweep over a
    plain block (10)^b is one move instead of b/2 small rounds."""

    def try_cross(self):
        r = self.right
        if self.q == 1 and r and r[-1][0] == (1, 0) and r[-1][1] >= 2:
            n = r.pop()[1]
            if n % 2:
                r.append([(1, 0), 1])
            r.append([(1, 0, 1, 0), n // 2])
        return rle.RLE.try_cross(self)


class Hybrid:
    def __init__(self, machine_a, f_watch=True, use_cf=True, memo=True):
        self.m = machine_a
        self.memo = {} if memo else None
        self.use_cf = use_cf
        self.fev = []          # (absolute step, cell read, context string)
        self.halted = None
        self.stats = {"cf": 0, "sim": 0, "memo": 0}
        self.hook = None       # hook(kind, sim, data): 'call' before a visit, 'ret' after it, 'exit' at the end

    # ------------------------------------------------------------------ one visit
    def go(self, l, t0, depth=0):
        """visit l starting at absolute step t0: returns (exit state, prefix, X, steps)"""
        l = tuple(l)
        if self.use_cf and cf.clean(l):
            self.stats["cf"] += 1
            X = cf.go(l)
            return 1, (0, 0), tuple(X), cf.steps(l) + 1
        if self.memo is not None and l in self.memo:
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
        nf = len(self.fev)
        res = self._run(sim, t0, stop_left=True, depth=depth)
        if res == "halt":
            raise rle.Halt()
        st, R = res
        pre, X = split_right(R)
        if X is None:
            raise RuntimeError(f"unexpected exit of a visit to {l}: state {st}, right {R[-8:]}")
        out = (st, pre, tuple(X), sim.steps)
        if self.memo is not None:
            self.memo[l] = out + ([(t - t0, y, c) for (t, y, c) in self.fev[nf:]],)
        return out

    # ------------------------------------------------------------------ the local simulation
    def _run(self, sim, t0, stop_left=False, depth=0, N=None, on_event=None):
        lastd = 0
        while True:
            if N is not None and sim.steps >= N:
                return None
            # a visit starts here?
            if sim.q == 0 and lastd == -1 and (not sim.right or sim.right[-1][0][0] == 0) and sim.pos >= (1 if stop_left else -10 ** 18):
                l = rle.suffix_list(sim)
                if l:
                    if on_event:
                        on_event(sim, l)
                    if self.hook:
                        self.hook("call", sim, l)
                    st, pre, X, T = self.go(l, t0 + sim.steps, depth + 1)
                    # replace the right part; the head moves onto the cell on its left
                    c = sim.pop_left()
                    sim.right = runs_of((pre, X))
                    sim.right.append([(c,), 1])
                    sim.pos -= 1
                    sim.steps += T
                    sim.q = st
                    lastd = -1
                    if stop_left and sim.pos < 0:
                        sim.pop_right()
                        if self.hook:
                            self.hook("exit", sim, st)
                        return st, sim.right
                    if self.hook:
                        self.hook("ret", sim, (st, pre, X))
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
                sim.pop_right()          # the blank cell read from the empty left stack
                if self.hook:
                    self.hook("exit", sim, sim.q)
                return sim.q, sim.right
            if not crossed and sim.q == 5 and q0 != 5:
                self.f_event(sim, t0)

    def f_event(self, sim, t0, halt=False):
        l, r = rle.near(sim, 12)
        self.fev.append((t0 + sim.steps, int(r[0]) if r else 0, l + "[F]" + r))

    # ------------------------------------------------------------------ the whole run
    def run(self, start_state, N, top=None):
        sim = FastRLE(self.m)
        sim.q = start_state
        self.top = []
        lo = [0]

        def ev(s, l):
            if s.pos <= lo[0]:
                self.top.append((s.steps, s.pos, list(l)))
        self.sim = sim

        try:
            r = self._run(sim, 0, stop_left=False, N=N, on_event=ev_wrap(ev, sim, lo))
        except rle.Halt:
            r = "halt"
        return r


def ev_wrap(ev, sim, lo):
    def f(s, l):
        # the left end: the head at the leftmost visited cell (the left stack holds only zeros or nothing)
        if all(all(c == 0 for c in w) for w, n in s.left):
            ev(s, l)
    return f


def split_right(R):
    """right stack (nearest last) = prefix cells + enc(X)"""
    toks = [list(t) for t in reversed(R)]
    # expand the first few cells into literals
    cells = []
    while toks and len(cells) < 6:
        w, n = toks[0]
        cells.extend(w)
        if n == 1:
            toks.pop(0)
        else:
            toks[0] = [w, n - 1]
    for k in range(0, min(4, len(cells)) + 1):
        pre = tuple(cells[:k])
        tail = [[(c,), 1] for c in cells[k:]] + toks
        X = parse_list(tail)
        if X is not None:
            return pre, X
    return None, None


def parse_list(toks):
    """toks (in tape order) = (10)^b1 1 (10)^b2 1 ... then nothing"""
    flat = []
    for w, n in toks:
        if w == (1, 0):
            flat.append(("a", n))
        elif len(w) % 2 == 0 and w == (1, 0) * (len(w) // 2):
            flat.append(("a", n * len(w) // 2))
        elif n > 200:
            return None
        else:
            for _ in range(n):
                flat.extend(("c", x) for x in w)
    while flat and flat[-1] == ("c", 0):
        flat.pop()
    out = []
    j = 0
    while j < len(flat):
        cnt = 0
        while j < len(flat):
            if flat[j][0] == "a":
                cnt += flat[j][1]
                j += 1
            elif flat[j] == ("c", 1) and j + 2 < len(flat) and flat[j + 1] == ("c", 0) and (flat[j + 2] == ("c", 1) or flat[j + 2][0] == "a"):
                cnt += 1
                j += 2
            else:
                break
        if j >= len(flat) or flat[j] != ("c", 1):
            return None
        out.append(cnt)
        j += 1
    return out


def run_machine(machine, N, log=None):
    fr, fa, st = frames.info(machine)
    h = Hybrid(fa)
    t0 = time.time()
    r = h.run(ord(st) - 65, N)
    return h, r, time.time() - t0


if __name__ == "__main__":
    m, N = sys.argv[1], float(sys.argv[2])
    h, r, secs = run_machine(m, N)
    print("steps", h.sim.steps, "halted" if r == "halt" else "", "top events", len(h.top), "F-events", len(h.fev),
          "stats", h.stats, f"{secs:.1f}s")
    for t in h.top[-5:]:
        print("top", t)
    for f in h.fev[:40]:
        print("F", f)
    if len(sys.argv) > 3:
        json.dump({"machine": m, "steps": h.sim.steps, "halted": h.halted, "top": h.top, "f_events": h.fev,
                   "stats": h.stats, "seconds": round(secs)}, open(sys.argv[3], "w"), indent=0)
