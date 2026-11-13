import Machine

/-! # Crossing rules of 1RB0LF_0RC0LC_1LA1LD_1RE1LC_---1RA_0LC0RD

The tape is the seven-cell word 0101111 in its rotations. Moving right behind the marker `1 0 1 1 1`, B and C cross a whole run of `0111110` (or of `1111100`) and leave it in another phase.

Written by `bbtools.symtm.prove` (the trace of a symbolic run, checked by the kernel). -/

namespace H66058

open TM

/-- Behind `1 0 1 1 1`, B crosses copies of `0111110`, leaving `1010111`. -/
theorem b_cross (n : Nat) (L R : Tape) :
    steps (13 * n) ⟨cons true (cons true (cons true (cons false (cons true (L))))), rep (n) [false, true, true, true, true, true, false] (R), .B⟩ = some ⟨rep (n) [true, true, true, false, true, false, true] (cons true (cons true (cons true (cons false (cons true (L)))))), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 13 ⟨app [] L, app [false, true, true, true, true, true, false] R, .B⟩ = some ⟨app [] (app [true, true, true, false, true, false, true] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 13) ⟨cons true (cons true (cons true (cons false (cons true (L))))), rep (n) [false, true, true, true, true, true, false] (R), .B⟩ = some ⟨rep (n) [true, true, true, false, true, false, true] (cons true (cons true (cons true (cons false (cons true (L)))))), R, .B⟩ :=
    cross_r trans c0 (n) (cons true (cons true (cons true (cons false (cons true (L)))))) (R)
  exact steps_congr trans (a := (n) * 13) (by omega) (h0)


/-- Behind `1 0 1 1 1 0`, C crosses copies of `1111100`, leaving `1010111`. -/
theorem c_cross (n : Nat) (L R : Tape) :
    steps (13 * n) ⟨cons false (cons true (cons true (cons true (cons false (cons true (L)))))), rep (n) [true, true, true, true, true, false, false] (R), .C⟩ = some ⟨cons false (rep (n) [true, true, true, false, true, false, true] (cons true (cons true (cons true (cons false (cons true (L))))))), R, .C⟩ := by
  have c0 : ∀ L R : Tape, steps 13 ⟨app [false] L, app [true, true, true, true, true, false, false] R, .C⟩ = some ⟨app [false] (app [true, true, true, false, true, false, true] L), R, .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 13) ⟨cons false (cons true (cons true (cons true (cons false (cons true (L)))))), rep (n) [true, true, true, true, true, false, false] (R), .C⟩ = some ⟨cons false (rep (n) [true, true, true, false, true, false, true] (cons true (cons true (cons true (cons false (cons true (L))))))), R, .C⟩ :=
    cross_r trans c0 (n) (cons true (cons true (cons true (cons false (cons true (L)))))) (R)
  exact steps_congr trans (a := (n) * 13) (by omega) (h0)


end H66058
