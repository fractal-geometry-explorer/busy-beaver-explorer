import Machine

/-! # Shift rules of 1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_0LF1RA

Proved from symbolic traces by `bbtools.symtm.prove` (written by `py/leanfiles.py`); each holds for every value of the counts and every tape in the contexts. -/

namespace H132322

open TM

/-- C erases a block of 1s leftwards and stops on the 0 before it. -/
theorem erase (n : Nat) (L R : Tape) :
    steps (n + 1) ⟨rep (n) [true] (cons false (L)), cons true (R), .C⟩ = some ⟨L, cons false (cons false (rep (n) [false] (R))), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [false] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨rep (n) [true] (cons false (L)), cons true (R), .C⟩ = some ⟨cons false (L), cons true (rep (n) [false] (R)), .C⟩ :=
    cross_l trans c0 (n) (cons false (L)) (R)
  have h1 : steps 1 ⟨cons false (L), cons true (rep (n) [false] (R)), .C⟩ = some ⟨L, cons false (cons false (rep (n) [false] (R))), .C⟩ := rfl
  exact steps_congr trans (a := (n) * 1 + (1)) (by omega) (steps_seq trans h0 (h1))

/-- D fills a run of 0s rightwards with 1s. -/
theorem fill (n : Nat) (L R : Tape) :
    steps (n) ⟨L, rep (n) [false] (cons true (R)), .D⟩ = some ⟨rep (n) [true] (L), cons true (R), .D⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [] L, app [false] R, .D⟩ = some ⟨app [] (app [true] L), R, .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨L, rep (n) [false] (cons true (R)), .D⟩ = some ⟨rep (n) [true] (L), cons true (R), .D⟩ :=
    cross_r trans c0 (n) (L) (cons true (R))
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

/-- F walks left over 0s. -/
theorem walk (n : Nat) (L R : Tape) :
    steps (n) ⟨rep (n) [false] (cons true (L)), cons false (R), .F⟩ = some ⟨cons true (L), cons false (rep (n) [false] (R)), .F⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [false] L, app [false] R, .F⟩ = some ⟨L, app [false] (app [false] R), .F⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨rep (n) [false] (cons true (L)), cons false (R), .F⟩ = some ⟨cons true (L), cons false (rep (n) [false] (R)), .F⟩ :=
    cross_l trans c0 (n) (cons true (L)) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

/-- B crosses pairs `1 1` rightwards, rewriting each as `1 0`. -/
theorem pairs (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [true, true] (R), .B⟩ = some ⟨rep (n) [false, true] (L), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .B⟩ = some ⟨app [] (app [false, true] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [true, true] (R), .B⟩ = some ⟨rep (n) [false, true] (L), R, .B⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- C on a separator 0 walks left through a block of 1s, moving the block one cell right. -/
theorem shift (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨rep (n) [true] (L), cons false (R), .C⟩ = some ⟨L, cons false (rep (n) [true] (R)), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [true] L, app [false] R, .C⟩ = some ⟨L, app [false] (app [true] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨rep (n) [true] (L), cons false (R), .C⟩ = some ⟨L, cons false (rep (n) [true] (R)), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 3) (by omega) (h0)

end H132322
