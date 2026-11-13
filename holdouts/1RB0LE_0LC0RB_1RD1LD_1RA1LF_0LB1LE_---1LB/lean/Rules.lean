import Machine

/-! # Shift rules of 1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB

Proved from symbolic traces by `bbtools.symtm.prove` (written by `py/leanfiles.py`); each holds for every value of the counts and every tape in the contexts. -/

namespace H38215

open TM

/-- B erases a block of 1s rightwards. -/
theorem bclear (n : Nat) (L R : Tape) :
    steps (n) ⟨L, rep (n) [true] (R), .B⟩ = some ⟨rep (n) [false] (L), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .B⟩ = some ⟨app [] (app [false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨L, rep (n) [true] (R), .B⟩ = some ⟨rep (n) [false] (L), R, .B⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

/-- E walks left over a block of 1s and stops on the 0 before it. -/
theorem ewalk (n : Nat) (L R : Tape) :
    steps (n + 1) ⟨rep (n) [true] (cons false (L)), cons true (R), .E⟩ = some ⟨L, cons false (cons true (rep (n) [true] (R))), .E⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [true] L, app [true] R, .E⟩ = some ⟨L, app [true] (app [true] R), .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨rep (n) [true] (cons false (L)), cons true (R), .E⟩ = some ⟨cons false (L), cons true (rep (n) [true] (R)), .E⟩ :=
    cross_l trans c0 (n) (cons false (L)) (R)
  have h1 : steps 1 ⟨cons false (L), cons true (rep (n) [true] (R)), .E⟩ = some ⟨L, cons false (cons true (rep (n) [true] (R))), .E⟩ := rfl
  exact steps_congr trans (a := (n) * 1 + (1)) (by omega) (steps_seq trans h0 (h1))

end H38215
