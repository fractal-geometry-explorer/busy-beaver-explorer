import Machine

/-! # Shift rules of 1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD

Proved from symbolic traces by `bbtools.symtm.prove` (written by `py/leanfiles.py`); each holds for every value of the counts and every tape in the contexts. -/

namespace H140108

open TM

/-- E erases a block of 1s leftwards: `0 1^n E>1` becomes `E>0 0^(n+1)`. -/
theorem erase (n : Nat) (L R : Tape) :
    steps (n + 1) ⟨rep (n) [true] (cons false (L)), cons true (R), .E⟩ = some ⟨L, cons false (cons false (rep (n) [false] (R))), .E⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [true] L, app [true] R, .E⟩ = some ⟨L, app [true] (app [false] R), .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨rep (n) [true] (cons false (L)), cons true (R), .E⟩ = some ⟨cons false (L), cons true (rep (n) [false] (R)), .E⟩ :=
    cross_l trans c0 (n) (cons false (L)) (R)
  have h1 : steps 1 ⟨cons false (L), cons true (rep (n) [false] (R)), .E⟩ = some ⟨L, cons false (cons false (rep (n) [false] (R))), .E⟩ := rfl
  exact steps_congr trans (a := (n) * 1 + (1)) (by omega) (steps_seq trans h0 (h1))

/-- F fills a run of 0s rightwards with 1s. -/
theorem fill (n : Nat) (L R : Tape) :
    steps (n) ⟨L, rep (n) [false] (cons true (R)), .F⟩ = some ⟨rep (n) [true] (L), cons true (R), .F⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [] L, app [false] R, .F⟩ = some ⟨app [] (app [true] L), R, .F⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨L, rep (n) [false] (cons true (R)), .F⟩ = some ⟨rep (n) [true] (L), cons true (R), .F⟩ :=
    cross_r trans c0 (n) (L) (cons true (R))
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

/-- D crosses pairs `1 1` rightwards, rewriting each as `1 0`. -/
theorem pairs (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [true, true] (R), .D⟩ = some ⟨rep (n) [false, true] (L), R, .D⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .D⟩ = some ⟨app [] (app [false, true] L), R, .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [true, true] (R), .D⟩ = some ⟨rep (n) [false, true] (L), R, .D⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- E on a separator 0 walks left through a block of 1s, moving the block one cell right. -/
theorem shift (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨rep (n) [true] (L), cons false (R), .E⟩ = some ⟨L, cons false (rep (n) [true] (R)), .E⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [true] L, app [false] R, .E⟩ = some ⟨L, app [false] (app [true] R), .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨rep (n) [true] (L), cons false (R), .E⟩ = some ⟨L, cons false (rep (n) [true] (R)), .E⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 3) (by omega) (h0)

end H140108
