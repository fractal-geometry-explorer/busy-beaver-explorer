import Machine

/-! # Shift rules: the head crosses a run of a repeated word, for any length of the run

Proved by `bbtools.symtm.prove` (re-run `py/` scripts or symtm to regenerate). -/

namespace H41157

open TM

/-- State C runs right through a block of 1s (`L C> (1)^n R` becomes `L (1)^n C> R`.) -/
theorem cross_ones_right (n : Nat) (L R : Tape) :
    steps (n) ⟨L, rep (n) [true] (R), .C⟩ = some ⟨rep (n) [true] (L), R, .C⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .C⟩ = some ⟨app [] (app [true] L), R, .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨L, rep (n) [true] (R), .C⟩ = some ⟨rep (n) [true] (L), R, .C⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

/-- State F runs left through a block of 1s (`L (1)^n F> 1 R` becomes `L F> 1 (1)^n R`.) -/
theorem cross_ones_left (n : Nat) (L R : Tape) :
    steps (n) ⟨rep (n) [true] (L), cons true (R), .F⟩ = some ⟨L, cons true (rep (n) [true] (R)), .F⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [true] L, app [true] R, .F⟩ = some ⟨L, app [true] (app [true] R), .F⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨rep (n) [true] (L), cons true (R), .F⟩ = some ⟨L, cons true (rep (n) [true] (R)), .F⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

end H41157
