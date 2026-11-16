import Machine

/-! # Visit laws of 1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB--- (right side)

Every theorem below is one row of a token-level visit law (mined from the run by `py/vislaws.c`, written by
`py/gen_visit2.py`): what one visit does to a stream that starts with the token, given what the nested visits of the
rest of the stream do.  Rows are exact for every stream (the hypotheses are about the rest only). -/

namespace H55410

open TM

/-- One visit of the stream `x` (right of the head's cell) in state `q`: back out on the left in state `r`, leaving
`x'`; the cell it lands on and everything left of it are untouched. -/
def Vis (q : St) (x : Tape) (r : St) (x' : Tape) : Prop :=
  ∀ (a : Bool) (L : Tape), ∃ t, steps t ⟨cons a L, x, q⟩ = some ⟨L, cons a x', r⟩

/-- `C` entering `000 x`, no nested visit: out in state A, leaving `100 x'`.  (In the run: 11 times in the first 30,000,000 steps, first at step 689712.) -/
theorem v_C_000_none {x : Tape}  :
    Vis .C (cons false (cons false (cons false x))) .A (cons true (cons false (cons false x))) := by
  intro a L
  have s0 : steps 1 ⟨cons a L, cons false (cons false (cons false x)), .C⟩ = some ⟨L, cons a (cons true (cons false (cons false x))), .A⟩ := rfl
  exact ⟨_, s0⟩

/-- `C` entering `010 x`, no nested visit: out in state A, leaving `110 x'`.  (In the run: 16029 times in the first 30,000,000 steps, first at step 1018330.) -/
theorem v_C_010_none {x : Tape}  :
    Vis .C (cons false (cons true (cons false x))) .A (cons true (cons true (cons false x))) := by
  intro a L
  have s0 : steps 1 ⟨cons a L, cons false (cons true (cons false x)), .C⟩ = some ⟨L, cons a (cons true (cons true (cons false x))), .A⟩ := rfl
  exact ⟨_, s0⟩

/-- `C` entering `100 x`, nested visits C→A: out in state D, leaving `010 x'`.  (In the run: 10688 times in the first 30,000,000 steps, first at step 859440.) -/
theorem v_C_100_Ca {x x1 : Tape} (h1 : Vis .C x .A x1) :
    Vis .C (cons true (cons false (cons false x))) .D (cons false (cons true (cons false x1))) := by
  intro a L
  have s0 : steps 7 ⟨cons a L, cons true (cons false (cons false x)), .C⟩ = some ⟨cons true (cons false (cons true (cons a L))), x, .C⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons true (cons a L)))
  have s1 : steps 5 ⟨cons false (cons true (cons a L)), cons true x1, .A⟩ = some ⟨L, cons a (cons false (cons true (cons false x1))), .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `C` entering `100 x`, nested visits C→D: out in state D, leaving `010 x'`.  (In the run: 5346 times in the first 30,000,000 steps, first at step 1314894.) -/
theorem v_C_100_Cd {x x1 : Tape} (h1 : Vis .C x .D x1) :
    Vis .C (cons true (cons false (cons false x))) .D (cons false (cons true (cons false x1))) := by
  intro a L
  have s0 : steps 7 ⟨cons a L, cons true (cons false (cons false x)), .C⟩ = some ⟨cons true (cons false (cons true (cons a L))), x, .C⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons true (cons a L)))
  have s1 : steps 5 ⟨cons false (cons true (cons a L)), cons true x1, .D⟩ = some ⟨L, cons a (cons false (cons true (cons false x1))), .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `C` entering `110 x`, no nested visit: out in state A, leaving `100 x'`.  (In the run: 16025 times in the first 30,000,000 steps, first at step 1166250.) -/
theorem v_C_110_none {x : Tape}  :
    Vis .C (cons true (cons true (cons false x))) .A (cons true (cons false (cons false x))) := by
  intro a L
  have s0 : steps 5 ⟨cons a L, cons true (cons true (cons false x)), .C⟩ = some ⟨L, cons a (cons true (cons false (cons false x))), .A⟩ := rfl
  exact ⟨_, s0⟩

end H55410
