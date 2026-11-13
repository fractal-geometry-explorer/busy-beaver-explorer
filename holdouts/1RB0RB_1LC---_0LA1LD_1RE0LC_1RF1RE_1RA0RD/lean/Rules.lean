import Machine

/-! The passes of 1RB0RB_1LC---_0LA1LD_1RE0LC_1RF1RE_1RA0RD, found and proved by `bbtools.symtm` for every n and every tape around (L, R). In Lean the left tape is listed from the head outward. -/

namespace H126123

open TM

/-- Going left, C rewrites every pair 11 as 01, carrying a 1 along: `(11)^n C> 1` becomes `C> 1 (01)^n` in 2n steps. -/
theorem left_pass (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [true, true] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [false, true] (R)), .C⟩ := by
  have hn : (n) * 2 = 2 * n := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [false, true] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [true, true] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [false, true] (R)), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

/-- Going right in D, every 0101 becomes 1110: `D> (0101)^n` becomes `(1110)^n D>`. -/
theorem right_D (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨L, rep (n) [false, true, false, true] (R), .D⟩ = some ⟨rep (n) [false, true, true, true] (L), R, .D⟩ := by
  have hn : (n) * 4 = 4 * n := by omega
  have c0 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true, false, true] R, .D⟩ = some ⟨app [] (app [false, true, true, true] L), R, .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨L, rep (n) [false, true, false, true] (R), .D⟩ = some ⟨rep (n) [false, true, true, true] (L), R, .D⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

/-- Going right in E, every 0101 becomes 1011: `E> (0101)^n` becomes `(1011)^n E>`. -/
theorem right_E (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨L, rep (n) [false, true, false, true] (R), .E⟩ = some ⟨rep (n) [true, true, false, true] (L), R, .E⟩ := by
  have hn : (n) * 4 = 4 * n := by omega
  have c0 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true, false, true] R, .E⟩ = some ⟨app [] (app [true, true, false, true] L), R, .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨L, rep (n) [false, true, false, true] (R), .E⟩ = some ⟨rep (n) [true, true, false, true] (L), R, .E⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

/-- E crosses runs of 1 unchanged. -/
theorem right_ones (n : Nat) (L R : Tape) :
    steps (n) ⟨L, rep (n) [true] (R), .E⟩ = some ⟨rep (n) [true] (L), R, .E⟩ := by
  have hn : (n) * 1 = n := by omega
  have c0 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .E⟩ = some ⟨app [] (app [true] L), R, .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨L, rep (n) [true] (R), .E⟩ = some ⟨rep (n) [true] (L), R, .E⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

end H126123
