import Machine

/-! # Shift rules: the head crosses a run of a repeated word, for any length of the run

Proved by `bbtools.symtm.prove` (re-run `py/` scripts or symtm to regenerate). -/

namespace H1965

open TM

/-- State D runs right through a block of 1s, erasing it (`L D> (1)^n R` becomes `L (0)^n D> R`.) -/
theorem erase_ones_D (n : Nat) (L R : Tape) :
    steps (n) ⟨L, rep (n) [true] (R), .D⟩ = some ⟨rep (n) [false] (L), R, .D⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .D⟩ = some ⟨app [] (app [false] L), R, .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨L, rep (n) [true] (R), .D⟩ = some ⟨rep (n) [false] (L), R, .D⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

/-- State F runs right through a block of 1s, erasing it (`L F> (1)^n R` becomes `L (0)^n F> R`.) -/
theorem erase_ones_F (n : Nat) (L R : Tape) :
    steps (n) ⟨L, rep (n) [true] (R), .F⟩ = some ⟨rep (n) [false] (L), R, .F⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .F⟩ = some ⟨app [] (app [false] L), R, .F⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨L, rep (n) [true] (R), .F⟩ = some ⟨rep (n) [false] (L), R, .F⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

/-- State A runs right through a run of 10, filling it with 1s (`L A> (10)^n R` becomes `L (11)^n A> R`.) -/
theorem fill_10 (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [true, false] (R), .A⟩ = some ⟨rep (n) [true, true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .A⟩ = some ⟨app [] (app [true, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [true, false] (R), .A⟩ = some ⟨rep (n) [true, true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

end H1965
