"""Where a halt can come from: every configuration two steps before a halt of 1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB, as a Lean theorem.

usage: python3 holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/py/route.py        writes lean/Route.lean (checked by lean/check.sh)

The machine is run for two steps from every state and every content of the five cells around the head (two on the
left, three under and right of it), which is all that two steps and the halting read can see; the windows that halt
on the third read are collected per state and shortened to the cells that matter.  The Lean proof splits on the
same state and cells and lets `simp` run the steps, so it does not trust this enumeration.
"""
import itertools
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.machine import Machine, STATES  # noqa: E402

M = "1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB"
NS = "H113677"
CELLS = ["l1", "l0", "r0", "r1", "r2"]
LEAN_CELL = {"l1": "c0.l 1", "l0": "c0.l 0", "r0": "c0.r 0", "r1": "c0.r 1", "r2": "c0.r 2"}
SHOW = {"l1": "two left", "l0": "left", "r0": "under the head", "r1": "right", "r2": "two right"}


def windows():
    """state -> set of 5-cell windows (l1, l0, r0, r1, r2) from which the machine halts on its third read."""
    m = Machine.parse(M)
    out = {}
    for q in range(m.n):
        for vals in itertools.product((0, 1), repeat=5):
            tape = dict(zip([-2, -1, 0, 1, 2], vals))
            h, s, ok = 0, q, True
            for _ in range(2):
                tr = m.table[s][tape[h]]
                if tr is None:
                    ok = False
                    break
                w, d, s = tr
                tape[h] = w
                h += d
            if ok and m.table[s][tape[h]] is None:
                out.setdefault(STATES[q], set()).add(vals)
    return out


def shorten(S):
    """Patterns (cell -> value) covering exactly the windows in S, by dropping cells while that stays exact."""
    terms = [dict(zip(CELLS, v)) for v in sorted(S)]
    changed = True
    while changed:
        changed = False
        for t in list(terms):
            for c in list(t):
                t2 = {k: v for k, v in t.items() if k != c}
                free = [x for x in CELLS if x not in t2]
                if all(tuple({**t2, **dict(zip(free, v))}[x] for x in CELLS) in S
                       for v in itertools.product((0, 1), repeat=len(free))):
                    terms.remove(t)
                    if t2 not in terms:
                        terms.append(t2)
                    changed = True
                    break
            if changed:
                break
    return terms


def main():
    pats = [(q, t) for q, S in sorted(windows().items()) for t in shorten(S)]
    disj = []
    words = []
    for q, t in pats:
        cs = sorted(t.items(), key=lambda kv: CELLS.index(kv[0]))
        disj.append("(" + " ∧ ".join([f"c0.st = .{q}"] + [f"{LEAN_CELL[c]} = {'true' if v else 'false'}" for c, v in cs]) + ")")
        words.append(f"{q} with " + ", ".join(f"{v} {SHOW[c]}" for c, v in cs))
    concl = " ∨\n      ".join(disj) if disj else "False"
    text = f"""import Machine

/-! # Where a halt of {M} can come from

Written by `py/route.py`.  `halt_route`: if the machine halts on its third step from a configuration `c0` (two
ordinary steps, then a configuration with no transition), then `c0` is one of the patterns below.  So a run reaches
a halt only through one of them; a proof of non-halting only has to rule these out.  The proof splits on the state
and on the five cells around the head and lets `simp` run the steps (kernel-checked). -/

set_option linter.unusedSimpArgs false

namespace {NS}

open TM

/-- Two steps before a halt the machine is in one of: {'; '.join(words)}. -/
theorem halt_route (c0 c1 c2 : Config) (h1 : step c0 = some c1) (h2 : step c1 = some c2)
    (h3 : step c2 = none) :
      {concl} := by
  obtain ⟨l, r, s⟩ := c0
  cases s <;> cases ha : r 0 <;> cases hb : r 1 <;> cases hc : r 2 <;> cases hd : l 0 <;> cases he : l 1 <;>
    simp [step, TM.step, trans, ha, hb, hc, hd, he, cons, tail] at h1 <;> subst h1 <;>
    simp [step, TM.step, trans, ha, hb, hc, hd, he, cons, tail] at h2 <;> subst h2 <;>
    simp_all [step, TM.step, trans, cons, tail]

end {NS}
"""
    with open(os.path.join(HERE, "..", "lean", "Route.lean"), "w") as f:
        f.write(text)
    print("; ".join(words))


if __name__ == "__main__":
    main()
