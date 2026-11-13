import Machine

/-! # Shift rules: the head crosses a run of a repeated word, for any length of the run

Proved by `bbtools.symtm.prove` (re-run `py/` scripts or symtm to regenerate). -/

namespace H129887

open TM

/-- State D runs left through the periodic block a = 1^5 0 1^2 0 at the left end, rewriting each copy (`L (111110110)^n D> 1 R` becomes `L D> 1 (101101101)^n R`.) -/
theorem cross_a_left (n : Nat) (L R : Tape) :
    steps (11 * n) ⟨rep (n) [false, true, true, false, true, true, true, true, true] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [true, false, true, true, false, true, true, false, true] (R)), .D⟩ := by
  have c0 : ∀ L R : Tape, steps 11 ⟨app [false, true, true, false, true, true, true, true, true] L, app [true] R, .D⟩ = some ⟨L, app [true] (app [true, false, true, true, false, true, true, false, true] R), .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 11) ⟨rep (n) [false, true, true, false, true, true, true, true, true] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [true, false, true, true, false, true, true, false, true] (R)), .D⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 11) (by omega) (h0)

/-- State E runs left through the same periodic block read in the other phase (`L (011011111)^n E> 0 R` becomes `L E> 0 (110110110)^n R`.) -/
theorem cross_a_left_E (n : Nat) (L R : Tape) :
    steps (11 * n) ⟨rep (n) [true, true, true, true, true, false, true, true, false] (L), cons false (R), .E⟩ = some ⟨L, cons false (rep (n) [true, true, false, true, true, false, true, true, false] (R)), .E⟩ := by
  have c0 : ∀ L R : Tape, steps 11 ⟨app [true, true, true, true, true, false, true, true, false] L, app [false] R, .E⟩ = some ⟨L, app [false] (app [true, true, false, true, true, false, true, true, false] R), .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 11) ⟨rep (n) [true, true, true, true, true, false, true, true, false] (L), cons false (R), .E⟩ = some ⟨L, cons false (rep (n) [true, true, false, true, true, false, true, true, false] (R)), .E⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 11) (by omega) (h0)

/-- State D runs left through a run of 110 (`L (110)^n D> 1 R` becomes `L D> 1 (101)^n R`.) -/
theorem cross_b_left (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨rep (n) [false, true, true] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [true, false, true] (R)), .D⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [false, true, true] L, app [true] R, .D⟩ = some ⟨L, app [true] (app [true, false, true] R), .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨rep (n) [false, true, true] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [true, false, true] (R)), .D⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 3) (by omega) (h0)

end H129887
