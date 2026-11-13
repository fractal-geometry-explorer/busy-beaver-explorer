import Machine

/-! # Recoding rules of 1RB---_0RC0LF_1LD0RE_1RC0LB_1RD1RA_1LB0LC

The tape is a list of runs of `001` separated by `0001`, written in that form after a leftward sweep and in the complemented form `110` / `1110` after a rightward one. Moving right, E, D, C, A turn each word into its complement, a whole run at once.

Written by `bbtools.symtm.prove` (the trace of a symbolic run, checked by the kernel). -/

namespace H29687

open TM

/-- E crosses copies of `001`, leaving `110`. -/
theorem e_recode3 (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨L, rep (n) [false, false, true] (R), .E⟩ = some ⟨rep (n) [false, true, true] (L), R, .E⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [] L, app [false, false, true] R, .E⟩ = some ⟨app [] (app [false, true, true] L), R, .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨L, rep (n) [false, false, true] (R), .E⟩ = some ⟨rep (n) [false, true, true] (L), R, .E⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 3) (by omega) (h0)


/-- D crosses copies of `010`, leaving `101`. -/
theorem d_recode3 (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨L, rep (n) [false, true, false] (R), .D⟩ = some ⟨rep (n) [true, false, true] (L), R, .D⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [] L, app [false, true, false] R, .D⟩ = some ⟨app [] (app [true, false, true] L), R, .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨L, rep (n) [false, true, false] (R), .D⟩ = some ⟨rep (n) [true, false, true] (L), R, .D⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 3) (by omega) (h0)


/-- C crosses copies of `100`, leaving `011`. -/
theorem c_recode3 (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨L, rep (n) [true, false, false] (R), .C⟩ = some ⟨rep (n) [true, true, false] (L), R, .C⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [] L, app [true, false, false] R, .C⟩ = some ⟨app [] (app [true, true, false] L), R, .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨L, rep (n) [true, false, false] (R), .C⟩ = some ⟨rep (n) [true, true, false] (L), R, .C⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 3) (by omega) (h0)


/-- A crosses copies of `0001`, leaving `1101`. -/
theorem a_recode4 (n : Nat) (L R : Tape) :
    steps (6 * n) ⟨L, rep (n) [false, false, false, true] (R), .A⟩ = some ⟨rep (n) [true, false, true, true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 6 ⟨app [] L, app [false, false, false, true] R, .A⟩ = some ⟨app [] (app [true, false, true, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 6) ⟨L, rep (n) [false, false, false, true] (R), .A⟩ = some ⟨rep (n) [true, false, true, true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 6) (by omega) (h0)


/-- E crosses copies of `1000`, leaving `1110`. -/
theorem e_recode4 (n : Nat) (L R : Tape) :
    steps (6 * n) ⟨L, rep (n) [true, false, false, false] (R), .E⟩ = some ⟨rep (n) [false, true, true, true] (L), R, .E⟩ := by
  have c0 : ∀ L R : Tape, steps 6 ⟨app [] L, app [true, false, false, false] R, .E⟩ = some ⟨app [] (app [false, true, true, true] L), R, .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 6) ⟨L, rep (n) [true, false, false, false] (R), .E⟩ = some ⟨rep (n) [false, true, true, true] (L), R, .E⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 6) (by omega) (h0)


/-- Moving left, C turns copies of `0111` back into `0001`. -/
theorem c_restore (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨rep (n) [true, true, true, false] (L), cons false (R), .C⟩ = some ⟨L, cons false (rep (n) [false, false, false, true] (R)), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [true, true, true, false] L, app [false] R, .C⟩ = some ⟨L, app [false] (app [false, false, false, true] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨rep (n) [true, true, true, false] (L), cons false (R), .C⟩ = some ⟨L, cons false (rep (n) [false, false, false, true] (R)), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)


end H29687
