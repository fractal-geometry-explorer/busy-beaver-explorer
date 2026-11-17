import Edge

/-!
# 1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB: halting at the right end of the tape

A right sweep that enters the last block of 1s in state E stops the machine at the end of the tape exactly when the
block has length 1 mod 3: `edge_stops` for length 3n + 1, and for lengths 3n + 2 and 3n + 3 the head turns back in a
state that does not halt (`edge_B_runs`, `edge_E_runs`).  Written by hand on the rules of `Edge.lean`; kernel only.
-/

namespace H56057

open TM

/-- Length 3n + 1: after 3n + 3 steps the machine is in D on a 0, which has no transition. -/
theorem edge_stops (n : Nat) (L : Tape) :
    ∃ c, steps (3 * n + 3) ⟨L, rep n [true, true, true] (cons true blank), .E⟩ = some c ∧ step c = none :=
  ⟨_, edge_halt n L, by simp [step, TM.step, trans, cons]⟩

/-- Length 3n + 2: the head turns back in A on a 1, and the machine takes another step. -/
theorem edge_B_runs (n : Nat) (L : Tape) :
    ∃ c, steps (3 * n + 3) ⟨L, rep n [true, true, true] (cons true (cons true blank)), .E⟩ = some c ∧
      step c ≠ none :=
  ⟨_, edge_B n L, by simp [step, TM.step, trans, cons]⟩

/-- Length 3n + 3: the head turns back in D on a 1, and the machine takes another step. -/
theorem edge_E_runs (n : Nat) (L : Tape) :
    ∃ c, steps (3 * n + 4) ⟨L, rep (n + 1) [true, true, true] blank, .E⟩ = some c ∧ step c ≠ none :=
  ⟨_, edge_E n L, by simp [step, TM.step, trans, cons]⟩

end H56057
