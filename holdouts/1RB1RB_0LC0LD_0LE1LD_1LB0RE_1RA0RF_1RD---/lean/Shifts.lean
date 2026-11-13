import Machine

/-! # Shift rules: the head crosses a run of a repeated word, for any length of the run

Proved by `bbtools.symtm.prove` (re-run `py/` scripts or symtm to regenerate). -/

namespace H181063

open TM

/-- State B runs left through a run of 10 (`L (10)^n B> 1 R` becomes `L B> 1 (10)^n R`.) -/
theorem cross_10_left (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [false, true] (L), cons true (R), .B⟩ = some ⟨L, cons true (rep (n) [true, false] (R)), .B⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .B⟩ = some ⟨L, app [true] (app [true, false] R), .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [false, true] (L), cons true (R), .B⟩ = some ⟨L, cons true (rep (n) [true, false] (R)), .B⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- State A runs right through a run of 01 (`L A> (01)^n R` becomes `L (01)^n A> R`.) -/
theorem cross_01_right (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨L, rep (n) [false, true] (R), .A⟩ = some ⟨rep (n) [true, false] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [true, false] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨L, rep (n) [false, true] (R), .A⟩ = some ⟨rep (n) [true, false] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

/-- State D runs left through a run of 01 (`L (01)^n D> 0 R` becomes `L D> 0 (01)^n R`.) -/
theorem cross_01_left (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [true, false] (L), cons false (R), .D⟩ = some ⟨L, cons false (rep (n) [false, true] (R)), .D⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .D⟩ = some ⟨L, app [false] (app [false, true] R), .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [true, false] (L), cons false (R), .D⟩ = some ⟨L, cons false (rep (n) [false, true] (R)), .D⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

end H181063
