import Machine

/-!
# 1RB---_0RC1RD_1LD1LF_1LE0RB_1RF1LD_1LA0LC: shift rules


Each theorem is written by `tools/py/bbtools/symtm.py` (`prove`) from a symbolic run and holds for every count
and every tape `L`, `R` beyond the cells shown.
-/

namespace H2968

open TM

/-- Moving right, B and D turn each pair `1 1` into `1 0`. -/
theorem bsweep (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [true, true] (R), .B⟩ = some ⟨rep (n) [false, true] (L), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .B⟩ = some ⟨app [] (app [false, true] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [true, true] (R), .B⟩ = some ⟨rep (n) [false, true] (L), R, .B⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- Moving left, F and C turn each pair `1 1` into `1 0` (read left to right). -/
theorem fsweep (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [true, true] (L), cons true (R), .F⟩ = some ⟨L, cons true (rep (n) [true, false] (R)), .F⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .F⟩ = some ⟨L, app [true] (app [true, false] R), .F⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [true, true] (L), cons true (R), .F⟩ = some ⟨L, cons true (rep (n) [true, false] (R)), .F⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- Moving left, D and E fill an alternating stretch `0 1 0 1` into solid 1s. -/
theorem dfill (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [true, false] (L), cons false (R), .D⟩ = some ⟨L, cons false (rep (n) [true, true] (R)), .D⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .D⟩ = some ⟨L, app [false] (app [true, true] R), .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [true, false] (L), cons false (R), .D⟩ = some ⟨L, cons false (rep (n) [true, true] (R)), .D⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- The same fill in the other phase. -/
theorem efill (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [false, true] (L), cons true (R), .E⟩ = some ⟨L, cons true (rep (n) [true, true] (R)), .E⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .E⟩ = some ⟨L, app [true] (app [true, true] R), .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [false, true] (L), cons true (R), .E⟩ = some ⟨L, cons true (rep (n) [true, true] (R)), .E⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

end H2968
