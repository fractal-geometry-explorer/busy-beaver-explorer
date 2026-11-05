"""An accelerated simulator for the two-stack form (py/twostack.py): frames memoized with symbolic inputs.

In the call-stack reading (py/callstack.py) an entry v<n> of the right stack is a frame.  Running a frame to its
return is a function of the frame and of the left stack L (b is the top of L, a the entry below it):

    gap >= 1:   (R1) pop b, pop a, push 0, run the frame (a+2)<b> to its return; gap -= 2
    gap == 0:   push the frame's value and return
    gap == -1:  (R2) needs value x >= 1; pop a, push 0; value <- a + 2, gap <- x - 2; take 1 off the caller's value

(an entry popped from below the bottom of L is -1).  A frame never reads its caller: it only takes k off the caller's
value in total, and the caller is suspended meanwhile, so the caller checks value >= k when the frame returns (if
not, the machine gets stuck there).  The one exception is the end entry with value 0 as caller: R2 then makes the
frame the new end entry.  The frames called by the end entry are therefore run by `end_child`, which handles that
case itself (their own callees go through the memo).

Memo.  A frame reads L only by popping, top down.  Most popped values are only moved (a becomes the value a + 2, which
is later pushed back); only some are inspected: a popped b (is it 0, how many turns), a value that becomes a gap in
R2, a value that a callee took something off.  So a frame is run symbolically: its inputs are its value and the
entries of L it pops, each a symbol, and a symbol is made concrete (and the value recorded) only when it is
inspected.  The memo is a decision tree per gap n: each inner node names the input to inspect next, each leaf is

    (d, P, k, steps, counts, events, last)

meaning: pop d entries, push P (constants or input + offset), take k off the caller, in `steps` two-stack steps;
`last` is the offset of the frame's last R2.  This is exact: the run is deterministic, so the same answers to the same
questions give the same computation.  Callees of a frame being computed go through the memo too, so a hit inside a
symbolic computation asks its questions of the caller's symbols, which may make them concrete in turn.

Logged: every step at which a frame other than the end entry is taken down to value 0 by its callees (a near miss:
one more R2 under it, or an odd gap of its own, would get the machine stuck), and counts of R2 steps, frames taken
down to 1, R2 with own value 1, end entries taken to 0 and replaced.

usage:
  python3 py/accel.py run STEPS [REPORT]  run from blank until STEPS two-stack steps (at an end turn), a line at every
                                          power of REPORT (default 10)
  python3 py/accel.py check STEPS         three-way check up to STEPS: the interpreter without memo against
                                          twostack.zstep at every step, and the memoized run against both at every
                                          end turn (configuration, step count, counts, events)
"""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.setrecursionlimit(1_000_000)

C_R2, C_TO1, C_X1, C_ZERO = range(4)
NC = 4


class Stuck(Exception):
    pass


class Ctx:
    """A stack being worked on.  The top context holds L itself (concrete, -1 below the bottom).  A context made
    for a fresh frame computation holds what the frame pushed (W) above the d entries it has popped from its
    caller's stack; its values are ints or symbols (j, off) = input j + off, input -1 being the frame's value and
    input i >= 0 the i-th entry popped."""
    __slots__ = ("W", "d", "parent", "vin", "conc", "key")

    def __init__(self, W, parent=None, vin=None):
        self.W = W
        self.d = 0
        self.parent = parent
        self.vin = vin
        self.conc = {}
        self.key = []

    def pop(self):
        if self.W:
            return self.W.pop()
        i = self.d
        self.d += 1
        return -1 if self.parent is None else (i, 0)

    def view(self, j):
        """The entry j below the top, without popping."""
        W = self.W
        if j < len(W):
            return W[-1 - j]
        return -1 if self.parent is None else (self.d + j - len(W), 0)

    def concrete(self, x):
        if type(x) is int:
            return x
        j, off = x
        c = self.conc.get(j)
        if c is None:
            pv = self.vin if j == -1 else self.parent.view(j)
            c = self.parent.concrete(pv)
            self.conc[j] = c
            self.key.append((j, c))
        return c + off


def shift(x, off):
    if type(x) is int:
        return x + off
    return (x[0], x[1] + off)


class Sim:
    def __init__(self, memo=True, trace=None):
        self.memo = {} if memo else None
        self.steps = 0
        self.counts = [0] * NC
        self.events = []        # (step, kind, info), global
        self.leaves = 0
        self.trace = trace      # without memo only: called after every step with the configuration
        self.rs = [] if trace else None

    def run(self, Y, v, n):
        """Run the frame v<n> (v in Y's terms, n an int) to its return on the stack Y.  Returns (k, last step of
        the frame's own R2)."""
        if self.memo is None:
            return self._run(Y, v, n)
        node = self.memo.get(n)
        while type(node) is list:
            j = node[0]
            node = node[1].get(Y.concrete(v if j == -1 else Y.view(j)))
        if node is None:
            X = Ctx([], Y, v)
            s0, e0 = self.steps, len(self.events)
            c0 = list(self.counts)
            k, last = self._run(X, (-1, 0), n)
            leaf = (X.d, tuple(X.W), k, self.steps - s0,
                    tuple(a - b for a, b in zip(self.counts, c0)),
                    tuple((s - s0, kd, info) for s, kd, info in self.events[e0:]),
                    None if last is None else last - s0)
            self.store(n, X.key, leaf)
            self.apply(Y, v, leaf, False)
            return k, last
        s0 = self.steps
        self.apply(Y, v, node, True)
        return node[2], None if node[6] is None else s0 + node[6]

    def store(self, n, key, leaf):
        self.leaves += 1
        if not key:
            self.memo[n] = leaf
            return
        node = self.memo.get(n)
        if node is None:
            node = self.memo[n] = [key[0][0], {}]
        for i, (j, c) in enumerate(key):
            assert node[0] == j
            nxt = node[1].get(c)
            if i == len(key) - 1:
                assert nxt is None
                node[1][c] = leaf
            else:
                if nxt is None:
                    nxt = node[1][c] = [key[i + 1][0], {}]
                node = nxt

    def apply(self, Y, v, leaf, hit):
        d, P, k, st, cnt, ev, last = leaf
        if P:
            ins = {}
            for x in P:
                if type(x) is not int:
                    j = x[0]
                    if j not in ins:
                        ins[j] = v if j == -1 else Y.view(j)
            out = [x if type(x) is int else shift(ins[x[0]], x[1]) for x in P]
        for _ in range(d):
            Y.pop()
        if P:
            Y.W.extend(out)
        if hit:
            if ev:
                s0 = self.steps
                self.events.extend((s0 + o, kd, info) for o, kd, info in ev)
            self.steps += st
            c = self.counts
            for i in range(NC):
                c[i] += cnt[i]

    def _run(self, X, v, n, endchild=None):
        """The frame v<n> on the stack X, step by step (callees through `run`).  endchild: the Top whose end entry
        is the caller (then R2 takes 1 off the end entry directly, or makes this frame the new end entry)."""
        k = 0
        last = None
        rs = self.rs
        if rs is not None:
            rs.append([v, n, 0])
        while True:
            if n >= 1:
                b = X.concrete(X.pop())
                a = X.pop()
                X.W.append(0)
                self.steps += 1
                if b == 0:
                    X.W.append(shift(a, 2))
                    if rs is not None:
                        rs[-1][1] = n - 2
                        self.trace(self)
                else:
                    if rs is not None:
                        rs[-1][1] = n - 2
                        rs.append([shift(a, 2), b, 0])
                        self.trace(self)
                        rs.pop()
                    kk, kl = self.run(X, shift(a, 2), b)
                    if kk:
                        cv = X.concrete(v)
                        if cv < kk:
                            raise Stuck(("caller below 0", cv, n - 2, kk, self.steps))
                        v = cv - kk
                        if v == 1:
                            self.counts[C_TO1] += 1
                        elif v == 0:
                            self.counts[C_ZERO] += 1
                            self.events.append((kl, "zero", (n - 2, kk)))
                        if rs is not None:
                            rs[-1][0] = v
                n -= 2
            elif n == 0:
                X.W.append(v)
                if rs is not None:
                    rs.pop()
                return k, last
            else:
                cv = X.concrete(v)
                if cv < 1:
                    raise Stuck(("own value 0 at R2", cv, n, self.steps))
                if cv == 1:
                    self.counts[C_X1] += 1
                a = X.pop()
                X.W.append(0)
                self.steps += 1
                self.counts[C_R2] += 1
                n = cv - 2
                v = shift(a, 2)
                if endchild is not None:
                    if endchild.endv >= 1:
                        endchild.endv -= 1
                        if endchild.endv == 0:
                            endchild.end_zero += 1
                    else:
                        # a, x<-1>, 0<end>  ->  0, (a+2)<end>
                        endchild.endv = v
                        endchild.end_replaced += 1
                        if rs is not None:
                            rs.pop()
                            self.trace(self)
                        return None, None
                else:
                    k += 1
                    last = self.steps
                if rs is not None:
                    rs[-1] = [v, n, k]
                    self.trace(self)


class Top:
    """The whole run: L in a top context, the end entry's value endv; the end entry turns forever."""

    def __init__(self, memo=True, trace=None):
        from callstack import start
        from twostack import END, cursor
        z = start()
        i = cursor(z)
        self.sim = Sim(memo, trace)
        self.L = Ctx([v for v, _ in z[:i]])
        R = z[i:]
        assert len(R) == 2 and R[1][1] is END, "start shape: one frame above the end entry"
        self.endv = R[1][0]
        self.end_zero = 0
        self.end_replaced = 0
        self.sim.top = self
        self.sim._run(self.L, R[0][0], R[0][1], endchild=self)

    def config(self, rs=()):
        """The row of the two-stack form; rs: the frames being run, bottom first, as [value, gap, k of callee]."""
        row = [[x, 0] for x in self.L.W]
        vals = [[f[0], f[1]] for f in rs]
        for i in range(1, len(rs)):
            vals[i - 1][0] -= rs[i][2]
        return row + vals[::-1] + [[self.endv, None]]

    def end_turn(self):
        """One turn of the end entry: R1 at the end, and the frame it calls run to its return."""
        s, L = self.sim, self.L
        b = L.pop()
        a = L.pop()
        L.W.append(0)
        s.steps += 1
        if b == 0:
            L.W.append(a + 2)
            if s.rs is not None:
                s.trace(s)
            return
        if s.rs is not None:
            s.rs.append([a + 2, b, 0])
            s.trace(s)
            s.rs.pop()
        s._run(L, a + 2, b, endchild=self)


def check(T):
    """Returns a list of failures (empty if all agree)."""
    from twostack import norm, zstep
    from callstack import start
    fails = []
    # 1. no memo, traced, against zstep at every step
    state = {"z": norm(start()), "n": 0}

    def tr(sim):
        state["z"] = zstep(state["z"])
        state["n"] += 1
        got = norm(sim.top.config(sim.rs))
        if got != state["z"] and len(fails) < 5:
            fails.append(("step", state["n"], got[-6:], state["z"][-6:]))

    plain = Top(memo=False, trace=tr)
    while plain.sim.steps < T and not fails:
        plain.end_turn()
    nsteps = state["n"]
    # 2. memo against no memo (untraced) at every end turn
    a, b = Top(memo=True), Top(memo=False)
    nturns = 0
    while a.sim.steps < T and not fails:
        a.end_turn()
        b.end_turn()
        nturns += 1
        if (a.sim.steps, a.L.W, a.endv, a.sim.counts, a.sim.events) != (b.sim.steps, b.L.W, b.endv, b.sim.counts,
                                                                       b.sim.events):
            fails.append(("end turn", nturns, a.sim.steps, b.sim.steps))
    return fails, nsteps, nturns


def run(T, base=10, quiet=False):
    t = Top()
    s = t.sim
    nxt = base
    t0 = time.time()
    ne = 0
    while s.steps < T:
        t.end_turn()
        if not quiet:
            while len(s.events) > ne:
                print("  event", s.events[ne], flush=True)
                ne += 1
            if s.steps >= nxt:
                c = s.counts
                print(f"steps {s.steps:.4e} R2 {c[C_R2]} to1 {c[C_TO1]} x1 {c[C_X1]} zero {c[C_ZERO]} "
                      f"end0 {t.end_zero} endrep {t.end_replaced} |L| {len(t.L.W)} end {t.endv} "
                      f"leaves {s.leaves} {time.time() - t0:.1f}s", flush=True)
                while nxt <= s.steps:
                    nxt *= base
    return t


def main(argv):
    if argv[0] == "check":
        fails, n, turns = check(int(float(argv[1])))
        print(f"steps compared with zstep {n}, end turns compared memo/no memo {turns}, failures {fails}")
    elif argv[0] == "run":
        run(int(float(argv[1])), int(argv[2]) if len(argv) > 2 else 10)


if __name__ == "__main__":
    main(sys.argv[1:])
