"""Closed tape languages from windows of K cells *with a parity feature*, for machines whose tape is read in pairs.

A state of a side's automaton is (window, f): the window of the K nearest cells as in `bbtools.ctl` (`#` = blank from
here on), and f = the parity of the distance from the first cell to the nearest 0 of the non-blank part outward
(0 = the first cell is that 0, 1 = odd, 2 = there is no 0 before the blank region).  For a window that holds a 0 the
feature is determined by the window; for an all-ones window it says how the cells beyond are aligned, which plain
windows cannot.  The result is a pair of `TM.CTL.Auto` automata and a set of abstract configurations, checked by the
same closure test as `bbtools.ctl.check` / `TM.CTL.closed`.

usage: python3 fctl.py MACHINE K [M]                       sizes, closure, the halts it allows   (M: feature modulus, 2)
       python3 fctl.py MACHINE K M lean NAMESPACE [IMPORT]  the certificate as a Lean file
"""
import sys, os
from collections import deque
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "tools", "py"))
from bbtools import ctl
from bbtools.ctl import H, canon, val
from bbtools.machine import Machine, STATES

J = int(os.environ.get("FCTL_J", "0"))   # cells of context kept after the next 0


def push(x, st, K, MOD):
    """The state of the stream `x` followed by a stream in state `st`."""
    w1, f1 = st
    w = canon((x,) + w1[:K - 1])
    if w[0] == H:
        return (w, MOD)
    if x == 0:
        return (w, 0) if J == 0 else (w, (0, w[1:1 + J]))
    if f1 == MOD:
        return (w, MOD)
    return (w, (f1 + 1) % MOD) if J == 0 else (w, ((f1[0] + 1) % MOD, f1[1]))


class FAuto(ctl.Auto):
    def __init__(self, states, K, MOD):
        self.windows = list(states)
        self.index = {w: i for i, w in enumerate(self.windows)}
        self.edges = []
        for j, st in enumerate(self.windows):
            for x in (0, 1):
                p = push(x, st, K, MOD)
                if p in self.index and val(p[0][0]) == x:
                    self.edges.append((self.index[p], x, j))
        self.edges.sort()
        self.acc = [self.index[((H,) * K, MOD)]]
        self._pops = {}
        self._preds = {}
        for (a, x, b) in self.edges:
            self._pops.setdefault(a, []).append((x, b))
            self._preds.setdefault((b, x), []).append(a)

    def pops(self, q):
        out = list(self._pops.get(q, []))
        if q in self.acc and (0, q) not in out:
            out.append((0, q))
        return out

    def preds(self, q, x):
        return self._preds.get((q, x), [])


def search(machine, K, MOD=2, max_rounds=10000, verbose=False):
    m = Machine.parse(machine) if isinstance(machine, str) else machine
    blank = ((H,) * K, MOD)
    WL, WR = {blank}, {blank}
    for rnd in range(max_rounds):
        AL, AR = FAuto(sorted(WL, key=repr), K, MOD), FAuto(sorted(WR, key=repr), K, MOD)
        start = (0, AL.index[blank], AR.index[blank])
        seen = {start}
        todo = deque([start])
        need = set()
        while todo:
            s, ql, qr = todo.popleft()
            for x, qr2 in AR.pops(qr):
                t = m.table[s][x]
                if t is None:
                    continue
                w, d, s2 = t
                outs = []
                if d == 1:
                    p = push(w, AL.windows[ql], K, MOD)
                    if p not in AL.index:
                        need.add(("L", p)); continue
                    outs.append((s2, AL.index[p], qr2))
                else:
                    p1 = push(w, AR.windows[qr2], K, MOD)
                    if p1 not in AR.index:
                        need.add(("R", p1)); continue
                    for y, ql2 in AL.pops(ql):
                        p0 = push(y, p1, K, MOD)
                        if p0 not in AR.index:
                            need.add(("R", p0)); continue
                        outs.append((s2, ql2, AR.index[p0]))
                for n in outs:
                    if n not in seen:
                        seen.add(n); todo.append(n)
        if verbose:
            print(f"round {rnd}: {len(WL)} left, {len(WR)} right, {len(seen)} configurations, {len(need)} new",
                  file=sys.stderr)
        if not need:
            return AL, AR, sorted(seen)
        for side, p in need:
            (WL if side == "L" else WR).add(p)
    raise RuntimeError("no closed set within max_rounds")


def show(st, MOD=2):
    f = st[1]
    return "".join("01#"[a] for a in st[0]) + "/" + ("-" if f == MOD else str(f) if J == 0 else
                                                      str(f[0]) + ":" + "".join("01#"[a] for a in f[1]))


def lean_file(machine, K, MOD, ns, imp="Machine"):
    AL, AR, S = search(machine, K, MOD)
    assert ctl.check(machine, AL, AR, S)
    def auto(A, side, name):
        es = ctl.wrap([f"({a}, {'true' if x else 'false'}, {b})" for a, x, b in A.edges])
        return (f"/-- The {side} automaton, nearest cell first ({len(A.windows)} states: a window of {K} cells and the "
                f"parity of the distance to the next 0). -/\n"
                f"def {name} : TM.CTL.Auto := ⟨{es},\n  {A.acc}⟩")
    items = [f"(.{STATES[s]}, {a}, {b})" for s, a, b in S]
    CH = 400   # a list literal of thousands of items exceeds Lean's recursion depth: the set is given in parts
    parts = [items[i:i + CH] for i in range(0, len(items), CH)]
    ss = "\n\n".join(f"def certS{i} : List (St × Nat × Nat) := {ctl.wrap(p)}" for i, p in enumerate(parts))
    ss += ("\n\n/-- The " + str(len(S)) + " abstract configurations (state, left automaton state, right automaton "
           "state). -/\ndef certS : List (St × Nat × Nat) :=\n  " + " ++ ".join(f"certS{i}" for i in range(len(parts))))
    return f"""import {imp}

/-!
# A closed tape language for {machine}

Windows of {K} cells, each with the distance (mod {MOD}) to the next 0 outward.  Generated by `py/fctl.py`; do not
edit by hand.  The theorems that use it check it with `decide`.
-/

namespace {ns}

{auto(AL, "left", "certL")}

{auto(AR, "right", "certR")}

{ss}

/-- The right automaton's states that accept only the blank tape. -/
def certB : List Nat := {AR.blank_only()}

end {ns}
"""


def main(argv):
    text, K = argv[0], int(argv[1])
    MOD = int(argv[2]) if len(argv) > 2 else 2
    if len(argv) > 4 and argv[3] == "lean":
        sys.stdout.write(lean_file(text, K, MOD, argv[4], *argv[5:6])); return
    AL, AR, S = search(text, K, MOD, verbose=True)
    print(f"K={K} mod {MOD}: {len(AL.windows)} left states, {len(AR.windows)} right states, {len(S)} abstract "
          f"configurations; closed: {ctl.check(text, AL, AR, S)}")
    B = set(AR.blank_only())
    hs = ctl.halting(text, AR, S)
    bad = [h for h in hs if h[4] not in B]
    print(f"halting abstract configurations: {len(hs)}, of which {len(bad)} with non-blank tape after the head")
    for (s, ql, qr, x, qr2) in bad[:20]:
        print(f"  can halt: {STATES[s]} reading {x}, left {show(AL.windows[ql], MOD)}, right {show(AR.windows[qr], MOD)}")


if __name__ == "__main__":
    main(sys.argv[1:])
