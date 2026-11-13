import Machine

/-!
# 1RB0LE_0LC0RF_1LD1LC_1RA0RD_0LA1LA_1RD---: shift rules


Each theorem is written by `tools/py/bbtools/symtm.py` (`prove`) from a symbolic run and holds for every count
and every tape `L`, `R` beyond the cells shown.
-/

namespace H52729

open TM

/-- C crosses 1s to the left. -/
theorem cleft (n : Nat) (L R : Tape) :
    steps (n) ⟨rep (n) [true] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [true] (R)), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [true] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨rep (n) [true] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [true] (R)), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

/-- Moving right, D erases 1s. -/
theorem derase (n : Nat) (L R : Tape) :
    steps (n) ⟨L, rep (n) [true] (R), .D⟩ = some ⟨rep (n) [false] (L), R, .D⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .D⟩ = some ⟨app [] (app [false] L), R, .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨L, rep (n) [true] (R), .D⟩ = some ⟨rep (n) [false] (L), R, .D⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

/-- Moving left, A and E turn each pair `1 1` into `1 0`. -/
theorem aleft11 (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [true, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [true, false] (R)), .A⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [true, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [true, false] (R)), .A⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- Moving left, A and E erase each pair `1 0`. -/
theorem aleft10 (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [false, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [false, false] (R)), .A⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [false, false] R), .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [false, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [false, false] (R)), .A⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- Moving left, E and A turn each pair `1 1` into `0 1`. -/
theorem eleft (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [true, true] (L), cons true (R), .E⟩ = some ⟨L, cons true (rep (n) [false, true] (R)), .E⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .E⟩ = some ⟨L, app [true] (app [false, true] R), .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [true, true] (L), cons true (R), .E⟩ = some ⟨L, cons true (rep (n) [false, true] (R)), .E⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

end H52729
