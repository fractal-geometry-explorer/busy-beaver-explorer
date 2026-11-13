import Machine

/-!
# 1RB0RA_0RC0RE_1LD1LF_1LE0LC_1RA0LD_0RA---: the leftward pass over the tail

The right part of the tape is a tail of `110` blocks that grows by one block per sweep. Moving left, the head in C
crosses it two blocks (6 cells) at a time in 20 steps, rewriting `110 110` into `001 001` (the right-to-left pass
of the bouncer; the next pass to the right writes the `110`s back). Each crossing reads one cell beyond the two
blocks, so the rule is stated with that cell (a 0, the last cell of the next block) in front.

Tapes are listed from the head outward, as in `tools/lean/TM/Basic.lean`.
-/

namespace H85142

open TM

/-- `cross_l` with a fixed word `x` between the head and the repeats (here the cell the crossing peeks at). -/
theorem cross_lx {s : Nat} {q : St} {x u w v : List Bool}
    (h : ∀ L R : Tape, steps s ⟨app x (app w L), app u R, q⟩ = some ⟨app x L, app u (app v R), q⟩) (k : Nat) :
    ∀ L R : Tape, steps (k * s) ⟨app x (rep k w L), app u R, q⟩ = some ⟨app x L, app u (rep k v R), q⟩ := by
  induction k with
  | zero => intro L R; simp
  | succ k ih =>
    intro L R
    have e : (k + 1) * s = s + k * s := by rw [Nat.succ_mul, Nat.add_comm]
    rw [e]
    have h₂ := ih L (app v R)
    rw [rep_app_comm] at h₂
    exact TM.steps_seq trans (h (rep k w L) R) h₂

/-- One crossing: `0 110110 C> 001` becomes `0 C> 001001 001` in 20 steps, for any tape beyond. -/
theorem pass_one (L R : Tape) :
    steps 20 ⟨app [false] (app [true, true, false, true, true, false] L), app [false, false, true] R, .C⟩ =
      some ⟨app [false] L, app [false, false, true] (app [false, false, true, false, false, true] R), .C⟩ := rfl

/-- The whole pass: `0 (110110)^n C> 001` becomes `0 C> 001 (001001)^n` in 20n steps, for every n. -/
theorem pass (n : Nat) (L R : Tape) :
    steps (n * 20) ⟨app [false] (rep n [true, true, false, true, true, false] L), app [false, false, true] R, .C⟩ =
      some ⟨app [false] L, app [false, false, true] (rep n [false, false, true, false, false, true] R), .C⟩ :=
  cross_lx pass_one n L R

end H85142
