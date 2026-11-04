"""Closed tape languages from windows of K cells, for any machine: a regular invariant of the run from blank tape.

Each side of the head is described by a finite automaton read outward from the head (nearest cell first).  Its
states are the windows of K cells that a side's stream can start with, over the letters 0, 1 and `#`, where `#`
means "this cell and every cell beyond it are 0".  A window W goes to W' on the letter x when W is the canonical
form of x followed by the first K - 1 letters of W' (a 0 in front of `#` becomes `#`); only the all-`#` window accepts
the blank tape.  An abstract configuration is (state, left automaton state, right automaton state) and stands for
every configuration whose streams those automata accept.

`search` grows the windows and the abstract configurations from the blank start until nothing new appears.
`check` is the closure test that `tools/lean/TM/CTL.lean` runs in Lean (`TM.CTL.check`), on the same data: from
each abstract configuration, every head symbol the right automaton allows and every transition must land in the set
again.  A halting transition is allowed but reported: `halting` lists the abstract configurations where one can
fire, and `blank_only` the automaton states whose language is the blank tape alone, which is how the Lean side
states where a halt can happen.

usage: python3 -m bbtools.ctl MACHINE K                     sizes, and the abstract configurations that can halt
       python3 -m bbtools.ctl MACHINE K lean NAMESPACE [IMPORT] > F
                                       the certificate as a Lean file (after `import IMPORT`, default Machine)
"""
import sys
from collections import deque

from .machine import Machine, STATES

H = 2   # the letter `#`


def canon(w):
    """A 0 in front of `#` (on the far side) is `#`."""
    w = list(w)
    for i in range(len(w) - 1, 0, -1):
        if w[i] == H and w[i - 1] == 0:
            w[i - 1] = H
    return tuple(w)


def val(a):
    return 0 if a == H else a


class Auto:
    """An automaton on windows: states are indices into `windows`; edges (q, x, q'); `acc` accepts blank tape."""

    def __init__(self, windows):
        self.windows = list(windows)
        self.index = {w: i for i, w in enumerate(self.windows)}
        K = len(self.windows[0])
        self.edges = []
        for i, w in enumerate(self.windows):
            for j, w2 in enumerate(self.windows):
                x = val(w[0])
                if canon((x,) + w2[:K - 1]) == w:
                    self.edges.append((i, x, j))
        self.acc = [self.index[(H,) * K]]

    def pops(self, q):
        """(head symbol, state of the rest) for every way the stream can start, as `TM.CTL.Auto.pops`."""
        out = [(x, q2) for (q1, x, q2) in self.edges if q1 == q]
        if q in self.acc:
            out.append((0, q))
        return out

    def preds(self, q, x):
        return [q1 for (q1, y, q2) in self.edges if q2 == q and y == x]

    def after(self, q, word):
        """The states after reading `word` from `q` (`TM.CTL.Auto.after`)."""
        qs = [q]
        for x in word:
            qs = [q2 for q1 in qs for (y, q2) in self.pops(q1) if y == x]
        return qs

    def blank_only(self):
        """The largest set of states with no edge on 1 and edges on 0 only into the set (`TM.CTL.blankOnly`)."""
        B = set(range(len(self.windows)))
        changed = True
        while changed:
            changed = False
            for (q1, x, q2) in self.edges:
                if q1 in B and (x == 1 or q2 not in B):
                    B.discard(q1)
                    changed = True
        return sorted(B)


def after_head(AR, S):
    """The right automaton's states for the streams after the head cell: reached from the abstract configurations by
    one symbol, and closed under edges (`Rt` of `TM.CTL.noDoubleZero`)."""
    Rt = {q2 for (_, _, qr) in S for (_, q2) in AR.pops(qr)}
    todo = list(Rt)
    while todo:
        for (_, q2) in AR.pops(todo.pop()):
            if q2 not in Rt:
                Rt.add(q2)
                todo.append(q2)
    return sorted(Rt)


def no_double_zero(AR, S):
    """Past the head cell, two 0s in a row lead only to blank tape (`TM.CTL.noDoubleZero`)."""
    B = set(AR.blank_only())
    return all(q2 in B for q in after_head(AR, S) for q2 in AR.after(q, [0, 0]))


def search(machine, K, max_rounds=100):
    """The least set of windows and abstract configurations closed under the machine's steps, from blank tape.

    Returns (left automaton, right automaton, abstract configurations as (state, left, right) index triples).
    A push onto a side uses the canonical window; if that window is not yet a state, it is added and the search
    starts again with the larger automata."""
    m = Machine.parse(machine) if isinstance(machine, str) else machine
    blank = (H,) * K
    WL, WR = {blank}, {blank}
    for _ in range(max_rounds):
        AL, AR = Auto(sorted(WL)), Auto(sorted(WR))
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
                    p = canon((w,) + AL.windows[ql][:K - 1])
                    if p not in AL.index:
                        need.add(("L", p))
                        continue
                    outs.append((s2, AL.index[p], qr2))
                else:
                    p1 = canon((w,) + AR.windows[qr2][:K - 1])
                    if p1 not in AR.index:
                        need.add(("R", p1))
                        continue
                    for y, ql2 in AL.pops(ql):
                        p0 = canon((y,) + p1[:K - 1])
                        if p0 not in AR.index:
                            need.add(("R", p0))
                            continue
                        outs.append((s2, ql2, AR.index[p0]))
                for n in outs:
                    if n not in seen:
                        seen.add(n)
                        todo.append(n)
        if not need:
            return AL, AR, sorted(seen)
        for side, p in need:
            (WL if side == "L" else WR).add(p)
    raise RuntimeError("no closed set within max_rounds")


def check(machine, AL, AR, S):
    """The closure test of `TM.CTL.check`: the start is in S and every non-halting abstract step lands in S."""
    m = Machine.parse(machine) if isinstance(machine, str) else machine
    Sset = set(S)
    if not any(s == 0 and ql in AL.acc and qr in AR.acc for (s, ql, qr) in S):
        return False
    for (s, ql, qr) in S:
        for x, qr2 in AR.pops(qr):
            t = m.table[s][x]
            if t is None:
                continue
            w, d, s2 = t
            if d == 1:
                if not any((s2, p, qr2) in Sset for p in AL.preds(ql, w)):
                    return False
            else:
                for y, ql2 in AL.pops(ql):
                    if not any((s2, ql2, p0) in Sset for p1 in AR.preds(qr2, w) for p0 in AR.preds(p1, y)):
                        return False
    return True


def halting(machine, AR, S):
    """The abstract configurations from which a halting transition can fire, with the right state after the head."""
    m = Machine.parse(machine) if isinstance(machine, str) else machine
    return [(s, ql, qr, x, qr2) for (s, ql, qr) in S for x, qr2 in AR.pops(qr) if m.table[s][x] is None]


def abstract(AL, AR, state, left, right):
    """The abstract configuration of a concrete one (state, left cells nearest first, right cells from the head;
    blank beyond), or None if a window along a side is not an automaton state.  Used by the tests against direct
    simulation: a run is covered when every configuration on it has its abstract configuration in the set."""
    K = len(AL.windows[0])

    def trim(cells):
        cells = list(cells)
        while cells and cells[-1] == 0:
            cells.pop()
        return cells

    def win(cells):
        return canon(tuple(cells[:K]) + (H,) * max(0, K - len(cells)))

    def start(A, cells):
        # accepted from its first window when the window at every position is a state (the edges then follow)
        cells = trim(cells)
        if all(win(cells[i:]) in A.index for i in range(len(cells) + 1)):
            return A.index[win(cells)]
        return None

    ql, qr = start(AL, left), start(AR, right)
    return None if ql is None or qr is None else (state, ql, qr)


def contains(AL, AR, S, state, left, right):
    """Is the concrete configuration in the set?"""
    return abstract(AL, AR, state, left, right) in set(S)


def wrap(items, indent="  ", width=118):
    """Lean list items, broken into lines of at most `width` characters."""
    lines, cur = [], ""
    for it in items:
        if cur and len(indent) + len(cur) + len(it) + 2 > width:
            lines.append(indent + cur.rstrip())
            cur = ""
        cur += it + ", "
    lines.append(indent + cur[:-2])
    return "[\n" + "\n".join(lines) + "]"


def lean_data(AL, AR, S, ns, name="cert"):
    """The automata and the set as Lean definitions `{name}L`, `{name}R`, `{name}S`, `{name}B` (states of the
    machine file in namespace `ns`, numbered A = 0, ...), with the windows as comments."""
    def auto(A, side):
        ws = wrap([f"{i} = {show(w)}" for i, w in enumerate(A.windows)], indent="")[2:-1]
        rows = [f"/-- The {side} automaton, nearest cell first; its states are the windows (`#` = blank from here on):",
                ws.replace(",\n", ",\n").rstrip() + ". -/"]
        es = wrap([f"({a}, {'true' if x else 'false'}, {b})" for a, x, b in A.edges])
        rows.append(f"def {name}{side[0].upper()} : TM.CTL.Auto := ⟨{es},\n  {A.acc}⟩")
        return "\n".join(rows)
    ss = wrap([f"(.{STATES[s]}, {a}, {b})" for s, a, b in S])
    return "\n\n".join([
        auto(AL, "left"), auto(AR, "right"),
        f"/-- The {len(S)} abstract configurations (state, left automaton state, right automaton state). -/\n"
        f"def {name}S : List (St × Nat × Nat) := {ss}",
        f"/-- The right automaton's states that accept only the blank tape. -/\ndef {name}B : List Nat := "
        f"{AR.blank_only()}",
        f"/-- The right automaton's states after the head cell. -/\ndef {name}Rt : List Nat := {after_head(AR, S)}"])


def lean_file(machine, K, ns, imp="Machine"):
    """A Lean file holding the certificate for `machine` with windows of K cells, after `import {imp}` (the
    machine's file from `bbtools.leangen`, namespace `ns`)."""
    text = machine if isinstance(machine, str) else machine.text
    AL, AR, S = search(text, K)
    return f"""import {imp}

/-!
# A closed tape language for {text}

Windows of {K} cells.  Generated by `bbtools.ctl.lean_file` (`tools/py/bbtools/ctl.py`); do not edit by hand.
The theorems that use it check it with `decide`.
-/

namespace {ns}

{lean_data(AL, AR, S, ns)}

end {ns}
"""


def show(w):
    return "".join("01#"[a] for a in w)


def main(argv):
    text, K = argv[0], int(argv[1])
    if len(argv) > 3 and argv[2] == "lean":
        sys.stdout.write(lean_file(text, K, argv[3], *argv[4:5]))
        return
    AL, AR, S = search(text, K)
    print(f"K={K}: {len(AL.windows)} left windows, {len(AR.windows)} right windows, {len(S)} abstract "
          f"configurations; closed: {check(text, AL, AR, S)}")
    print(f"past the head, 0 0 only in the blank region: {no_double_zero(AR, S)}")
    B = set(AR.blank_only())
    for (s, ql, qr, x, qr2) in halting(text, AR, S):
        print(f"  can halt: {STATES[s]} reading {x}, left {show(AL.windows[ql])}, right {show(AR.windows[qr])}"
              f"{'  (blank after the head)' if qr2 in B else ''}")


if __name__ == "__main__":
    main(sys.argv[1:])
