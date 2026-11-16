import Machine

/-! # Visit laws of 1RB1LE_0RC0RB_1RD1RF_1LA0LE_0LD0LB_---0RD (right side)

Every theorem below is one row of a token-level visit law (mined from the run by `py/vislaws.c`, written by
`py/gen_visit2.py`): what one visit does to a stream that starts with the token, given what the nested visits of the
rest of the stream do.  Rows are exact for every stream (the hypotheses are about the rest only). -/

namespace H65208

open TM

/-- One visit of the stream `x` (right of the head's cell) in state `q`: back out on the left in state `r`, leaving
`x'`; the cell it lands on and everything left of it are untouched. -/
def Vis (q : St) (x : Tape) (r : St) (x' : Tape) : Prop :=
  ∀ (a : Bool) (L : Tape), ∃ t, steps t ⟨cons a L, x, q⟩ = some ⟨L, cons a x', r⟩

/-- `B` entering `0000 x`, no nested visit: out in state D, leaving `0110 x'`.  (In the run: 17245 times in the first 1,000,000,000 steps, first at step 367121349.) -/
theorem v_B_0000_none {x : Tape}  :
    Vis .B (cons false (cons false (cons false (cons false x)))) .D (cons false (cons true (cons true (cons false x)))) := by
  intro a L
  have s0 : steps 5 ⟨cons a L, cons false (cons false (cons false (cons false x))), .B⟩ = some ⟨L, cons a (cons false (cons true (cons true (cons false x)))), .D⟩ := rfl
  exact ⟨_, s0⟩

/-- `B` entering `0110 x`, nested visits B→D: out in state D, leaving `0111 x'`.  (In the run: 17241 times in the first 1,000,000,000 steps, first at step 367121465.) -/
theorem v_B_0110_Bd {x x1 : Tape} (h1 : Vis .B x .D x1) :
    Vis .B (cons false (cons true (cons true (cons false x)))) .D (cons false (cons true (cons true (cons true x1)))) := by
  intro a L
  have s0 : steps 6 ⟨cons a L, cons false (cons true (cons true (cons false x))), .B⟩ = some ⟨cons false (cons true (cons true (cons false (cons a L)))), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons true (cons false (cons a L))))
  have s1 : steps 12 ⟨cons true (cons true (cons false (cons a L))), cons false x1, .D⟩ = some ⟨L, cons a (cons false (cons true (cons true (cons true x1)))), .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `B` entering `0111 x`, no nested visit: out in state D, leaving `0000 x'`.  (In the run: 17237 times in the first 1,000,000,000 steps, first at step 367121583.) -/
theorem v_B_0111_none {x : Tape}  :
    Vis .B (cons false (cons true (cons true (cons true x)))) .D (cons false (cons false (cons false (cons false x)))) := by
  intro a L
  have s0 : steps 7 ⟨cons a L, cons false (cons true (cons true (cons true x))), .B⟩ = some ⟨L, cons a (cons false (cons false (cons false (cons false x)))), .D⟩ := rfl
  exact ⟨_, s0⟩

end H65208
