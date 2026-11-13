import Machine

/-!
# 1RB0LF_1RC0RB_0RD1LE_0LE0RA_1LC1LA_0LD---: shift rules


Each theorem is written by `tools/py/bbtools/symtm.py` (`prove`) from a symbolic run and holds for every count
and every tape `L`, `R` beyond the cells shown.
-/

namespace H11596

open TM

/-- Moving right, D turns each `1 0 0 0` into `0 1 1 0`, four steps a word. -/
theorem dword (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨L, rep (n) [true, false, false, false] (R), .D⟩ = some ⟨rep (n) [false, true, true, false] (L), R, .D⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [] L, app [true, false, false, false] R, .D⟩ = some ⟨app [] (app [false, true, true, false] L), R, .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨L, rep (n) [true, false, false, false] (R), .D⟩ = some ⟨rep (n) [false, true, true, false] (L), R, .D⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

/-- Moving right, A turns each `0 0 0 1` into `1 1 0 0`. -/
theorem aword (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨L, rep (n) [false, false, false, true] (R), .A⟩ = some ⟨rep (n) [false, false, true, true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, false, false, true] R, .A⟩ = some ⟨app [] (app [false, false, true, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨L, rep (n) [false, false, false, true] (R), .A⟩ = some ⟨rep (n) [false, false, true, true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

/-- Moving right, C turns each `0 1 0 0` into `0 0 1 1`. -/
theorem cword (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨L, rep (n) [false, true, false, false] (R), .C⟩ = some ⟨rep (n) [true, true, false, false] (L), R, .C⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true, false, false] R, .C⟩ = some ⟨app [] (app [true, true, false, false] L), R, .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨L, rep (n) [false, true, false, false] (R), .C⟩ = some ⟨rep (n) [true, true, false, false] (L), R, .C⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

/-- Moving right, B turns each `0 0 1 0` into `1 0 0 1`. -/
theorem bword (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨L, rep (n) [false, false, true, false] (R), .B⟩ = some ⟨rep (n) [true, false, false, true] (L), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, false, true, false] R, .B⟩ = some ⟨app [] (app [true, false, false, true] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨L, rep (n) [false, false, true, false] (R), .B⟩ = some ⟨rep (n) [true, false, false, true] (L), R, .B⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

/-- Moving right, B erases 1s. -/
theorem berase (n : Nat) (L R : Tape) :
    steps (n) ⟨L, rep (n) [true] (R), .B⟩ = some ⟨rep (n) [false] (L), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .B⟩ = some ⟨app [] (app [false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨L, rep (n) [true] (R), .B⟩ = some ⟨rep (n) [false] (L), R, .B⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

/-- Moving left, E carries a 0 across the words `0 0 0 1`, eight steps a word. -/
theorem eshift (n : Nat) (L R : Tape) :
    steps (8 * n) ⟨rep (n) [true, false, false, false] (L), cons false (R), .E⟩ = some ⟨L, cons false (rep (n) [false, false, false, true] (R)), .E⟩ := by
  have c0 : ∀ L R : Tape, steps 8 ⟨app [true, false, false, false] L, app [false] R, .E⟩ = some ⟨L, app [false] (app [false, false, false, true] R), .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 8) ⟨rep (n) [true, false, false, false] (L), cons false (R), .E⟩ = some ⟨L, cons false (rep (n) [false, false, false, true] (R)), .E⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 8) (by omega) (h0)

/-- Moving left, D carries a 0 across the words `0 0 1 0`. -/
theorem dshift (n : Nat) (L R : Tape) :
    steps (8 * n) ⟨rep (n) [false, true, false, false] (L), cons false (R), .D⟩ = some ⟨L, cons false (rep (n) [false, false, true, false] (R)), .D⟩ := by
  have c0 : ∀ L R : Tape, steps 8 ⟨app [false, true, false, false] L, app [false] R, .D⟩ = some ⟨L, app [false] (app [false, false, true, false] R), .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 8) ⟨rep (n) [false, true, false, false] (L), cons false (R), .D⟩ = some ⟨L, cons false (rep (n) [false, false, true, false] (R)), .D⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 8) (by omega) (h0)

/-- Moving left, E fills `0 1` pairs into `1 1`. -/
theorem efill (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [true, false] (L), cons false (R), .E⟩ = some ⟨L, cons false (rep (n) [true, true] (R)), .E⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .E⟩ = some ⟨L, app [false] (app [true, true] R), .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [true, false] (L), cons false (R), .E⟩ = some ⟨L, cons false (rep (n) [true, true] (R)), .E⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- Moving left, C fills `1 0` pairs into `1 1`. -/
theorem cfill (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [false, true] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [true, true] (R)), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [true, true] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [false, true] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [true, true] (R)), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

end H11596
