import Machine

/-! The end of a halving chain of 1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA (see the README): a block of two ones at the
left end, in the shape the halvings come back to, leads to a halt. Proved for every tape around. -/

namespace H25221

open TM

/-- The halving chain ends in a halt at x = 2: from E> 0 1 1 0 0 1 0 the machine reaches D reading 0 with 1 next (D0 is the halting transition) in 7 steps, for every tape around. -/
theorem two_to_halt (L R : Tape) :
    steps (7) ⟨L, cons false (cons true (cons true (cons false (cons false (cons true (cons false (R))))))), .E⟩ = some ⟨cons true (L), cons false (cons true (cons false (cons true (cons true (cons false (R)))))), .D⟩ := by
  have h0 : steps 7 ⟨L, cons false (cons true (cons true (cons false (cons false (cons true (cons false (R))))))), .E⟩ = some ⟨cons true (L), cons false (cons true (cons false (cons true (cons true (cons false (R)))))), .D⟩ := rfl
  exact steps_congr trans (a := 7) (by omega) (h0)


/-- The configuration `two_to_halt` reaches has no next step: D reads 0, the halting transition. -/
theorem two_stuck (L R : Tape) :
    step ⟨cons true (L), cons false (cons true (cons false (cons true (cons true (cons false (R)))))), .D⟩ = none := rfl

end H25221
