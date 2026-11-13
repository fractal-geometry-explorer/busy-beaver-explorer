import Machine

/-! # Shift rules: the head crosses a run of a repeated word, for any length of the run

Proved by `bbtools.symtm.prove` (re-run `py/` scripts or symtm to regenerate). -/

namespace H139315

open TM

/-- State D runs left through a run of 110 (`L (110)^n D> 1 R` becomes `L D> 1 (011)^n R`.) -/
theorem cross_110_left (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨rep (n) [false, true, true] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [false, true, true] (R)), .D⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [false, true, true] L, app [true] R, .D⟩ = some ⟨L, app [true] (app [false, true, true] R), .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨rep (n) [false, true, true] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [false, true, true] (R)), .D⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 3) (by omega) (h0)

/-- State B runs left through a run of 011 (`L (011)^n B> 0 R` becomes `L B> 0 (101)^n R`.) -/
theorem cross_011_left (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨rep (n) [true, true, false] (L), cons false (R), .B⟩ = some ⟨L, cons false (rep (n) [true, false, true] (R)), .B⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [true, true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [true, false, true] R), .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨rep (n) [true, true, false] (L), cons false (R), .B⟩ = some ⟨L, cons false (rep (n) [true, false, true] (R)), .B⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 3) (by omega) (h0)

end H139315
