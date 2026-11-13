"""The proved rules chained along the actual run of 1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB, as one Lean theorem.

usage: python3 holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/py/table.py [BOUND]     writes lean/Table.lean
                                                                         (BOUND default 1e30)

`py/macro.py` replays the run as moves of the branch table from `O 14 37 11` (step 29,301).  With the ends of
`lean/Ends.lean` the table has a rule for every configuration the replay meets, so the chain is cut at the last macro
state before step BOUND.  `lean/Closed.lean` starts from that state, so any bound whose last state satisfies
the invariant `Good` will do (`py/closed.py` checks); 10^300 (2,280 moves) compiles in about 90 seconds as well.  Each move becomes the Lean rule (or `*_iter` lemma) with its concrete
arguments, and `table_run` chains them.  Lean checks each instance, so the chain does not trust the replay.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
import macro  # noqa: E402
from bbtools.symtm import prove  # noqa: E402
from branch import FORMS  # noqa: E402

NS = "H113677"
macro_M = "1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB"
BOUND = 1e30


def lean_cfg(f, P):
    return f"{f} " + " ".join(map(str, P))


def term(f, P):
    """The Lean proof of `∃ n, steps n (f P) = some (next)` for the move macro.move makes from (f, P)."""
    if f == "O":
        a, b, c = P
        if b == 0:
            return f"⟨_, ozero {a} {c - 3}⟩"
        return f"⟨_, oentry {a} {b - 6} {c - 2}⟩"
    if f == "S1":
        a, b, c = P
        if c >= 2:
            k = c // 2
            return f"cycle_iter {k} {a} {b - 2} {c - 2 * k}"
        return f"⟨_, oexit {a} {b - 6}⟩" if c == 1 else f"⟨_, sexit0 {a} {b - 3}⟩"
    if f == "RF":
        a, k, m = P
        if m >= 2:
            return f"rcyc_iter {m - 1} {a} {k} 0"
        return f"rend' {a} {(k - 1) // 2}" if k % 2 else f"rende' {a} {k // 2}"
    if f == "EF":
        a, q = P
        return f"⟨_, eentry {a - 7} {q - 5}⟩"
    if f == "T3":
        a, x, d, y, z, c = P
        if x == d == y == 0:
            return f"⟨0, by rw [t3_s1]; rfl⟩"
        if d >= 5:
            k = min(d // 5, c // 2)
            return f"cycle3_iter {k} {a} {x - 6} {d - 5 * k} {y - 6} {z - 6} {c - 2 * k}"
        off = {0: (5, 2, 2, 1), 1: (6, 5, 6, 2), 2: (6, 5, 6, 2), 3: (6, 5, 6, 3), 4: (6, 5, 6, 3)}[d]
        # binders in sorted order: a c x y z
        return f"⟨_, texit{d} {a} {c - off[3]} {x - off[0]} {y - off[1]} {z - off[2]}⟩"
    if f == "T2":
        a, x, y, c = P
        if c >= 2:
            k = c // 2
            return f"cycle2_iter {k} {a} {x - 6} {y - 6} {c - 2 * k}"
        return f"⟨_, t2exit{c} {a} {x - 2} {y - (10 if c == 0 else 12)}⟩"
    if f == "U3":
        a, x, y, z, c = P
        if c >= 2:
            k = c // 2
            return f"ucyc_iter {k} {a} {x - 2} {y - 6} {z - 6} {c - 2 * k}"
        return f"⟨_, uexit{c} {a} {x - 2} {y - 6} {z - (10 if c == 0 else 12)}⟩"
    if f == "RG":
        a, x, n, m = P
        if m >= 2:
            return f"gcyc_iter {m - 1} {a} {x} {n} 0"
        if n % 2:
            return f"gendo' {a - 3} {x - 6} {(n - 7) // 2}"
        return f"gend' {a - 2} {x} {n // 2}"
    if f == "RG3":
        a, x, y, n, m = P
        if m >= 2:
            return f"g3cyc_iter {m - 1} {a} {x} {y} {n} 0"
        if n % 2:
            return f"g3endo' {a - 7} {x - 10} {y - 2} {(n - 7) // 2}"
        return f"g3end' {a} {x} {y - 4} {n // 2 - 2}"
    raise ValueError(f)


def main():
    bound = float(sys.argv[1]) if len(sys.argv) > 1 else BOUND
    rows, esc = macro.replay(bound)
    assert esc is None, esc
    states = [(f, P) for _, f, P in rows]
    lines = []
    for i, (f, P) in enumerate(states[:-1]):
        g, Q = states[i + 1]
        lines.append(f"  obtain ⟨n{i}, h{i}⟩ : ∃ n, steps n ({lean_cfg(f, P)}) = some ({lean_cfg(g, Q)}) :=\n"
                     f"    {term(f, P)}")
    chain = f"h{len(states) - 2}"
    for i in reversed(range(len(states) - 2)):
        chain = f"steps_seq trans h{i} ({chain})"
    blank, fin = prove(macro_M, "blank_raw", "0^inf A> 0^inf", FORMS["O"]("14", "37", "11"), max_moves=40000,
                       max_seg=200, count_first=True,
                       doc="The first 29,301 steps from blank tape, as the run writes the tape.")
    assert str(fin.steps) == "29301"
    last = states[-1]
    t_last = rows[-1][0]
    text = f"""import Ends

/-! # The branch table along the run

`blank_O`: from blank tape the machine is in `O 14 37 11` at step 29,301 (a concrete run, by `rfl` in pieces).
`table_run`: from `O 14 37 11` the machine reaches
`{lean_cfg(*last)}`,
the last macro state before step {bound:.0e} (`py/macro.py` puts it at step {t_last:.6e}).  The chain has
{len(states) - 1} moves, each one rule of `Cycle.lean`, `Phase.lean`, `Branch.lean`, `Ends.lean` or a k-fold iterate,
with concrete arguments.  No configuration along the way lacks a rule; the chain stops only at the bound.

Generated by `py/table.py`. -/

namespace {NS}

open TM

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

""" + blank + f"""
/-- From blank tape the machine is in the odd-phase form `O 14 37 11` at step 29,301. -/
theorem blank_O : steps 29301 init = some (O 14 37 11) := blank_raw

/-- The branch table along the run, from `O 14 37 11` to the last macro state before the bound. -/
theorem table_run : ∃ n, steps n (O 14 37 11) = some ({lean_cfg(*last)}) := by
""" + "\n".join(lines) + f"""
  exact ⟨_, {chain}⟩

/-- From blank tape the machine reaches `{lean_cfg(*last)}` (step {t_last:.6e} by `py/macro.py`). -/
theorem table_from_blank : ∃ n, steps n init = some ({lean_cfg(*last)}) := by
  obtain ⟨n, h⟩ := table_run
  exact ⟨_, steps_seq trans blank_O h⟩

end {NS}
"""
    with open(os.path.join(HERE, "..", "lean", "Table.lean"), "w") as fh:
        fh.write(text)
    print(len(states) - 1, "moves; ends at", lean_cfg(*last), "step", t_last)


if __name__ == "__main__":
    main()
