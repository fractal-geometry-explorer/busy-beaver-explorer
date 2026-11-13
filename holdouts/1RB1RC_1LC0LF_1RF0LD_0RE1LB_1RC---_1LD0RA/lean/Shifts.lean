import Machine

/-! # Shift rules: the head crosses a run of a repeated word, for any length of the run

Proved by `bbtools.symtm.prove` (re-run `py/` scripts or symtm to regenerate). -/

namespace H147335

open TM

/-- State D runs left through the periodic block a = 11010 (`L (11010)^n D> 1 R` becomes `L D> 1 (01101)^n R`.) -/
theorem cross_a_left (n : Nat) (L R : Tape) :
    steps (9 * n) ⟨rep (n) [false, true, false, true, true] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [false, true, true, false, true] (R)), .D⟩ := by
  have c0 : ∀ L R : Tape, steps 9 ⟨app [false, true, false, true, true] L, app [true] R, .D⟩ = some ⟨L, app [true] (app [false, true, true, false, true] R), .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 9) ⟨rep (n) [false, true, false, true, true] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [false, true, true, false, true] (R)), .D⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 9) (by omega) (h0)

/-- State B runs left through a run of 110 (`L (110)^n B> 1 R` becomes `L B> 1 (110)^n R`.) -/
theorem cross_b_left (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨rep (n) [false, true, true] (L), cons true (R), .B⟩ = some ⟨L, cons true (rep (n) [true, true, false] (R)), .B⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [false, true, true] L, app [true] R, .B⟩ = some ⟨L, app [true] (app [true, true, false] R), .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨rep (n) [false, true, true] (L), cons true (R), .B⟩ = some ⟨L, cons true (rep (n) [true, true, false] (R)), .B⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 3) (by omega) (h0)

/-- State F runs right through a run of 110 (`L F> (110)^n R` becomes `L (011)^n F> R`.) -/
theorem cross_b_right (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨L, rep (n) [true, true, false] (R), .F⟩ = some ⟨rep (n) [true, true, false] (L), R, .F⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [] L, app [true, true, false] R, .F⟩ = some ⟨app [] (app [true, true, false] L), R, .F⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨L, rep (n) [true, true, false] (R), .F⟩ = some ⟨rep (n) [true, true, false] (L), R, .F⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 3) (by omega) (h0)

end H147335
