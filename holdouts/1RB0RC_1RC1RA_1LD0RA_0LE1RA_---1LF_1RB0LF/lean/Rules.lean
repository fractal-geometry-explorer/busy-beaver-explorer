import Machine

/-! Shift rules for 1RB0RC_1RC1RA_1LD0RA_0LE1RA_---1LF_1RB0LF, and a halting family: C going right over an even run of 1s followed by a 0 halts. Proved by `bbtools.symtm` (rules) and by hand from them; tapes in Lean are listed from the head outward. -/

namespace H21851

open TM

/-- C going right erases `11` pairs (C1 = 0RA, A1 = 0RC). -/
theorem right_C_11 (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [true, true] (R), .C⟩ = some ⟨rep (n) [false, false] (L), R, .C⟩ := by
  have hn : (n) * 2 = 2 * n := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .C⟩ = some ⟨app [] (app [false, false] L), R, .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [true, true] (R), .C⟩ = some ⟨rep (n) [false, false] (L), R, .C⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

/-- A going right erases `11` pairs. -/
theorem right_A_11 (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [true, true] (R), .A⟩ = some ⟨rep (n) [false, false] (L), R, .A⟩ := by
  have hn : (n) * 2 = 2 * n := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .A⟩ = some ⟨app [] (app [false, false] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [true, true] (R), .A⟩ = some ⟨rep (n) [false, false] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

/-- C going right over `1^(2n+2) 0` halts, whatever the tape around: it erases the ones, writes a 1 on the 0 and
goes left as D, D reads the 0 it left behind and goes left as E, and E reads another 0. -/
theorem halts_C_even (n : Nat) (L R : Tape) :
    TM.Halts trans ⟨L, rep (n + 1) [true, true] (cons false R), .C⟩ := by
  refine ⟨2 * (n + 1) + 2, ⟨rep n [false, false] L, cons false (cons false (cons true R)), .E⟩, ?_, rfl⟩
  have h2 : steps 2 ⟨rep (n + 1) [false, false] L, cons false R, .C⟩ =
      some ⟨rep n [false, false] L, cons false (cons false (cons true R)), .E⟩ := by
    simp only [rep_succ]; rfl
  exact steps_seq trans (right_C_11 (n + 1) L (cons false R)) h2

end H21851
