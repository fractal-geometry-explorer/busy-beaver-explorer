"""Rewrite ../lean/VisitRules.lean: the "eat" visit of the right-end bouncer, for all counts, and k visits in a row.

Between visits to the right end the head sweeps left and comes back.  In one recurring phase the tape right of the
irregular digit list reads  L 1^(a+3) (01011)^b (011)^c 0  with the head in D on the blank cell after it, and the
sweep turns inside the block of 1s: it eats three 1s, crosses (01011)^b and (011)^c both ways (the left sweep turns
(011)^c into (001)^c, the right sweep turns it back) and appends two copies of 011.  So

  eat:       L 1^(a+3) (01011)^b (011)^c 0 D> 0^inf  reaches  L 1^a (01011)^b (011)^(c+2) 0 D> 0^inf
             in 20b + 10c + 25 steps (for every a, b, c and every tape L; L is never read),
  eat_iter:  k visits in a row take  k(20b + 10c + 15) + 10k^2  steps and leave  1^a (01011)^b (011)^(c+2k).

The phase lasts until the block of 1s is used up; it is seen in the run for example from step 3.1e8 to 3.84e8
(b = 1,379, a from about 5,000 down to 171).  The single visit is proved by `tools/py/bbtools/symtm.py` (rfl steps and
the crossing lemmas); the regrouping and the induction are written out below.

usage: python3 holdouts/MACHINE/py/visit_rules.py   (from the repository root; then lean/check.sh)
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools import symtm  # noqa: E402
from bbtools.machine import Machine  # noqa: E402

M = "1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE"

START = "L (1)^a+3 (01011)^b (011)^c 0 D> 0^inf"
END = "L (1)^a (01011)^b 0 1 1 (011)^c 0 1 1 0 D> 0^inf"   # as the run writes it: (011)^(c+2) after regrouping

TAIL = r"""
/-- The three cells `0 1 1` next to the repeat, written on the left tape nearest first, are one more copy of it. -/
theorem w3_regroup (c : Nat) (X : Tape) :
    cons false (cons true (cons true (cons false (rep c [true, true, false]
      (cons true (cons true (cons false X))))))) = cons false (rep (c + 2) [true, true, false] X) := by
  show cons false (app [true, true, false] (rep c [true, true, false] (app [true, true, false] X))) = _
  rw [rep_app_comm]
  rfl

/-- One eat visit with the right end regrouped: `1^(a+3) (01011)^b (011)^c 0 D>` reaches `1^a (01011)^b (011)^(c+2) 0 D>`. -/
theorem eat_visit (a b c : Nat) (L : Tape) :
    steps (20 * b + 10 * c + 25)
      ⟨cons false (rep c [true, true, false] (rep b [true, true, false, true, false] (rep (a + 3) [true] L))), blank, .D⟩
    = some ⟨cons false (rep (c + 2) [true, true, false] (rep b [true, true, false, true, false] (rep a [true] L))), blank, .D⟩ := by
  have h := eat a b c L
  rw [w3_regroup] at h
  exact h

/-- Steps of `k` eat visits in a row starting with `(011)^c`. -/
def eatSteps (b : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, c => (20 * b + 10 * c + 25) + eatSteps b k (c + 2)

theorem eatSteps_eq (b : Nat) : ∀ k c, eatSteps b k c = k * (20 * b + 10 * c + 15) + 10 * (k * k) := by
  intro k
  induction k with
  | zero => intro c; simp [eatSteps]
  | succ k ih =>
    intro c
    rw [eatSteps, ih]
    simp only [Nat.succ_mul, Nat.mul_succ, Nat.mul_add]
    omega

/-- `k` eat visits in a row: `1^(a+3k) (01011)^b (011)^c 0 D>` reaches `1^a (01011)^b (011)^(c+2k) 0 D>` in
`k(20b + 10c + 15) + 10k²` steps, for every `a, b, c, k` and every tape `L` beyond the block of 1s. -/
theorem eat_iter (b : Nat) (L : Tape) : ∀ k a c,
    steps (k * (20 * b + 10 * c + 15) + 10 * (k * k))
      ⟨cons false (rep c [true, true, false] (rep b [true, true, false, true, false] (rep (a + 3 * k) [true] L))), blank, .D⟩
    = some ⟨cons false (rep (c + 2 * k) [true, true, false] (rep b [true, true, false, true, false] (rep a [true] L))), blank, .D⟩ := by
  intro k
  induction k with
  | zero => intro a c; simp
  | succ k ih =>
    intro a c
    rw [← eatSteps_eq, eatSteps, eatSteps_eq]
    have h1 := eat_visit (a + 3 * k) b c L
    rw [show a + 3 * k + 3 = a + 3 * (k + 1) by omega] at h1
    have h2 := ih a (c + 2)
    rw [show c + 2 + 2 * k = c + 2 * (k + 1) by omega] at h2
    exact TM.steps_seq trans h1 h2
"""


def main():
    m = Machine.parse(M)
    symtm.MAX_CARRY = 8
    th, fin = symtm.prove(m, "eat", START, END, rotate=True, count_first=True, max_seg=40,
                          doc="One eat visit, as the run writes the end configuration (proved by symtm).")
    lean = os.path.join(HERE, "..", "lean")
    ns = re.search(r"namespace (\w+)", open(os.path.join(lean, "Machine.lean")).read()).group(1)
    doc = (f"# {M}: the eat visit of the right-end bouncer\n\n" + __doc__.split("\n\nusage")[0].split("\n", 1)[1].strip()
           + "\n\nWritten by the folder's `py/visit_rules.py` with `tools/py/bbtools/symtm.py`; do not edit by hand.")
    text = symtm.rules_file("Machine", ns, [th + TAIL], doc)
    with open(os.path.join(lean, "VisitRules.lean"), "w") as f:
        f.write(text)
    print("eat:", fin, "steps", fin.steps)


if __name__ == "__main__":
    main()
