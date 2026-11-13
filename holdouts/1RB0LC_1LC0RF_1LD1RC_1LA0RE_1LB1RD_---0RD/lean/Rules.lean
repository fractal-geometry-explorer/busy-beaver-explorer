import Machine

/-!
# 1RB0LC_1LC0RF_1LD1RC_1LA0RE_1LB1RD_---0RD: shift rules


Each theorem is written by `tools/py/bbtools/symtm.py` (`prove`) from a symbolic run and holds for every count
and every tape `L`, `R` beyond the cells shown.
-/

namespace H174142

open TM

/-- C crosses 1s to the right. -/
theorem cright (n : Nat) (L R : Tape) :
    steps (n) ⟨L, rep (n) [true] (R), .C⟩ = some ⟨rep (n) [true] (L), R, .C⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .C⟩ = some ⟨app [] (app [true] L), R, .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨L, rep (n) [true] (R), .C⟩ = some ⟨rep (n) [true] (L), R, .C⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

/-- Moving left, C carries a pair of 0s across a block of 1s, five steps a cell. -/
theorem cleft (n : Nat) (L R : Tape) :
    steps (5 * n) ⟨rep (n) [true] (L), cons false (cons false (R)), .C⟩ = some ⟨L, cons false (cons false (rep (n) [true] (R))), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 5 ⟨app [true] L, app [false, false] R, .C⟩ = some ⟨L, app [false, false] (app [true] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 5) ⟨rep (n) [true] (L), cons false (cons false (R)), .C⟩ = some ⟨L, cons false (cons false (rep (n) [true] (R))), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 5) (by omega) (h0)

/-- Moving right, D turns each pair `1 1` into `0 1`. -/
theorem dright (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [true, true] (R), .D⟩ = some ⟨rep (n) [true, false] (L), R, .D⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .D⟩ = some ⟨app [] (app [true, false] L), R, .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [true, true] (R), .D⟩ = some ⟨rep (n) [true, false] (L), R, .D⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- Moving right, E turns each pair `1 1` into `1 0`. -/
theorem eright (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [true, true] (R), .E⟩ = some ⟨rep (n) [false, true] (L), R, .E⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .E⟩ = some ⟨app [] (app [false, true] L), R, .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [true, true] (R), .E⟩ = some ⟨rep (n) [false, true] (L), R, .E⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

end H174142
