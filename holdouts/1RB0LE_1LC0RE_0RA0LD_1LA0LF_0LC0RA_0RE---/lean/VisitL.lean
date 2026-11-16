import Machine

/-! # Visit laws of 1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE--- (left side)

Every theorem below is one row of a token-level visit law (mined from the run by `py/vislaws.c`, written by
`py/gen_visit2.py`): what one visit does to a stream that starts with the token, given what the nested visits of the
rest of the stream do.  Rows are exact for every stream (the hypotheses are about the rest only). -/

namespace H43701

open TM

/-- One visit of the stream `x` (left of the head's cell, nearest cell first) in state `q`: the head steps onto `x 0`
and the first time it comes back out on the right it is in state `r`, the stream is `x'`, and the cell it lands on
and everything right of it are untouched. -/
def VisL (q : St) (x : Tape) (r : St) (x' : Tape) : Prop :=
  ∀ (a : Bool) (R : Tape), ∃ t, steps t ⟨tail x, cons (x 0) (cons a R), q⟩ = some ⟨x', cons a R, r⟩

/-- `A` entering `000 x`, no nested visit: out in state B, leaving `100 x'`.  (In the run: 12 times in the first 30,000,000 steps, first at step 588436.) -/
theorem w_A_000_none {x : Tape}  :
    VisL .A (cons false (cons false (cons false x))) .B (cons true (cons false (cons false x))) := by
  intro a R
  have s0 : steps 1 ⟨cons false (cons false x), cons false (cons a R), .A⟩ = some ⟨cons true (cons false (cons false x)), cons a R, .B⟩ := rfl
  exact ⟨_, s0⟩

/-- `A` entering `010 x`, no nested visit: out in state B, leaving `110 x'`.  (In the run: 63681 times in the first 30,000,000 steps, first at step 693182.) -/
theorem w_A_010_none {x : Tape}  :
    VisL .A (cons false (cons true (cons false x))) .B (cons true (cons true (cons false x))) := by
  intro a R
  have s0 : steps 1 ⟨cons true (cons false x), cons false (cons a R), .A⟩ = some ⟨cons true (cons true (cons false x)), cons a R, .B⟩ := rfl
  exact ⟨_, s0⟩

/-- `A` entering `100 x`, nested visits A→B: out in state E, leaving `010 x'`.  (In the run: 42457 times in the first 30,000,000 steps, first at step 640616.) -/
theorem w_A_100_Ab {x x1 : Tape} (h1 : VisL .A x .B x1) :
    VisL .A (cons true (cons false (cons false x))) .E (cons false (cons true (cons false x1))) := by
  intro a R
  have s0 : steps 7 ⟨cons false (cons false x), cons true (cons a R), .A⟩ = some ⟨tail x, cons (x 0) (cons true (cons false (cons true (cons a R)))), .A⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons true (cons a R)))
  have s1 : steps 5 ⟨x1, cons true (cons false (cons true (cons a R))), .B⟩ = some ⟨cons false (cons true (cons false x1)), cons a R, .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `A` entering `100 x`, nested visits A→E: out in state E, leaving `010 x'`.  (In the run: 21226 times in the first 30,000,000 steps, first at step 798228.) -/
theorem w_A_100_Ae {x x1 : Tape} (h1 : VisL .A x .E x1) :
    VisL .A (cons true (cons false (cons false x))) .E (cons false (cons true (cons false x1))) := by
  intro a R
  have s0 : steps 7 ⟨cons false (cons false x), cons true (cons a R), .A⟩ = some ⟨tail x, cons (x 0) (cons true (cons false (cons true (cons a R)))), .A⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons true (cons a R)))
  have s1 : steps 3 ⟨x1, cons true (cons false (cons true (cons a R))), .E⟩ = some ⟨cons false (cons true (cons false x1)), cons a R, .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `A` entering `110 x`, no nested visit: out in state B, leaving `100 x'`.  (In the run: 63678 times in the first 30,000,000 steps, first at step 745474.) -/
theorem w_A_110_none {x : Tape}  :
    VisL .A (cons true (cons true (cons false x))) .B (cons true (cons false (cons false x))) := by
  intro a R
  have s0 : steps 3 ⟨cons true (cons false x), cons true (cons a R), .A⟩ = some ⟨cons true (cons false (cons false x)), cons a R, .B⟩ := rfl
  exact ⟨_, s0⟩

end H43701
