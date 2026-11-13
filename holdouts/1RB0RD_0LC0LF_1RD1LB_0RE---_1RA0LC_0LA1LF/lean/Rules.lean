import Machine

/-! Shift rules for 1RB0RD_0LC0LF_1RD1LB_0RE---_1RA0LC_0LA1LF, proved by `bbtools.symtm` for every n and every tape around; tapes in Lean are listed from the head outward. -/

namespace H106698

open TM

/-- A going right turns `(100)^n` into `(001)^n`. -/
theorem right_A_100 (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨L, rep (n) [true, false, false] (R), .A⟩ = some ⟨rep (n) [true, false, false] (L), R, .A⟩ := by
  have hn : (n) * 3 = 3 * n := by omega
  have c0 : ∀ L R : Tape, steps 3 ⟨app [] L, app [true, false, false] R, .A⟩ = some ⟨app [] (app [true, false, false] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨L, rep (n) [true, false, false] (R), .A⟩ = some ⟨rep (n) [true, false, false] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

/-- D going right turns `(001)^n` into `(010)^n`. -/
theorem right_D_001 (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨L, rep (n) [false, false, true] (R), .D⟩ = some ⟨rep (n) [false, true, false] (L), R, .D⟩ := by
  have hn : (n) * 3 = 3 * n := by omega
  have c0 : ∀ L R : Tape, steps 3 ⟨app [] L, app [false, false, true] R, .D⟩ = some ⟨app [] (app [false, true, false] L), R, .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨L, rep (n) [false, false, true] (R), .D⟩ = some ⟨rep (n) [false, true, false] (L), R, .D⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

/-- A going right turns `(1010)^n` into `(0101)^n`. -/
theorem right_A_1010 (n : Nat) (L R : Tape) :
    steps (6 * n) ⟨L, rep (n) [true, false, true, false] (R), .A⟩ = some ⟨rep (n) [true, false, true, false] (L), R, .A⟩ := by
  have hn : (n) * 6 = 6 * n := by omega
  have c0 : ∀ L R : Tape, steps 6 ⟨app [] L, app [true, false, true, false] R, .A⟩ = some ⟨app [] (app [true, false, true, false] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 6) ⟨L, rep (n) [true, false, true, false] (R), .A⟩ = some ⟨rep (n) [true, false, true, false] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

/-- D going right turns `(0101)^n` into `(1010)^n`. -/
theorem right_D_0101 (n : Nat) (L R : Tape) :
    steps (6 * n) ⟨L, rep (n) [false, true, false, true] (R), .D⟩ = some ⟨rep (n) [false, true, false, true] (L), R, .D⟩ := by
  have hn : (n) * 6 = 6 * n := by omega
  have c0 : ∀ L R : Tape, steps 6 ⟨app [] L, app [false, true, false, true] R, .D⟩ = some ⟨app [] (app [false, true, false, true] L), R, .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 6) ⟨L, rep (n) [false, true, false, true] (R), .D⟩ = some ⟨rep (n) [false, true, false, true] (L), R, .D⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

/-- E going right turns `(0101)^n` into `(1010)^n`. -/
theorem right_E_0101 (n : Nat) (L R : Tape) :
    steps (6 * n) ⟨L, rep (n) [false, true, false, true] (R), .E⟩ = some ⟨rep (n) [false, true, false, true] (L), R, .E⟩ := by
  have hn : (n) * 6 = 6 * n := by omega
  have c0 : ∀ L R : Tape, steps 6 ⟨app [] L, app [false, true, false, true] R, .E⟩ = some ⟨app [] (app [false, true, false, true] L), R, .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 6) ⟨L, rep (n) [false, true, false, true] (R), .E⟩ = some ⟨rep (n) [false, true, false, true] (L), R, .E⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

/-- A reading `1 1` halts in two steps: A1 = 0RD and D reads the second 1. -/
theorem halts_A_11 (L R : Tape) : TM.Halts trans ⟨L, cons true (cons true R), .A⟩ :=
  ⟨1, ⟨cons false L, cons true R, .D⟩, rfl, rfl⟩

/-- C reading `0 1` halts in two steps: C0 = 1RD and D reads the 1. -/
theorem halts_C_01 (L R : Tape) : TM.Halts trans ⟨L, cons false (cons true R), .C⟩ :=
  ⟨1, ⟨cons true L, cons true R, .D⟩, rfl, rfl⟩

end H106698
