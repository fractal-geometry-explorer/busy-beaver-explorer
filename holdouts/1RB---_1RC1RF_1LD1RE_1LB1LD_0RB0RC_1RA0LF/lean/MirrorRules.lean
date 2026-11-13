import MirrorMachine

/-! The two local rules of the tick, written by `bbtools.symtm.prove` (from `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/gen_clock.py`). -/

namespace H98843M

open TM

/-- The sweep: `0 0 0 0 E> 1^(6+4n) 0` becomes `0 0 0 1 0^(6+4n) F> 0`. -/
theorem rule_sweep (n : Nat) (L R : Tape) :
    steps (4 * n + 10) ⟨cons false (cons false (cons false (cons false (L)))), cons true (cons true (cons true (cons true (cons true (cons true (rep (4 * n) [true] (cons false (R)))))))), .E⟩ = some ⟨rep (4 * n) [false] (cons false (cons false (cons false (cons false (cons false (cons false (cons true (cons false (cons false (cons false (L))))))))))), cons false (R), .F⟩ := by
  have h0 : steps 10 ⟨cons false (cons false (cons false (cons false (L)))), cons true (cons true (cons true (cons true (cons true (cons true (rep (4 * n) [true] (cons false (R)))))))), .E⟩ = some ⟨cons false (cons false (cons false (cons false (cons false (cons false (cons true (cons false (cons false (cons false (L)))))))))), rep (4 * n) [true] (cons false (R)), .F⟩ := rfl
  have c1 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .F⟩ = some ⟨app [] (app [false] L), R, .F⟩ := fun _ _ => rfl
  have h1 : steps ((4 * n) * 1) ⟨cons false (cons false (cons false (cons false (cons false (cons false (cons true (cons false (cons false (cons false (L)))))))))), rep (4 * n) [true] (cons false (R)), .F⟩ = some ⟨rep (4 * n) [false] (cons false (cons false (cons false (cons false (cons false (cons false (cons true (cons false (cons false (cons false (L))))))))))), cons false (R), .F⟩ :=
    cross_r trans c1 (4 * n) (cons false (cons false (cons false (cons false (cons false (cons false (cons true (cons false (cons false (cons false (L))))))))))) (cons false (R))
  exact steps_congr trans (a := 10 + ((4 * n) * 1)) (by omega) (steps_seq trans h0 (h1))

/-- The merge: `0 0 0 1 E> 1` becomes `E> 1 1 1 1 1`. -/
theorem rule_merge (L R : Tape) :
    steps (14) ⟨cons true (cons false (cons false (cons false (L)))), cons true (R), .E⟩ = some ⟨L, cons true (cons true (cons true (cons true (cons true (R))))), .E⟩ := by
  have h0 : steps 14 ⟨cons true (cons false (cons false (cons false (L)))), cons true (R), .E⟩ = some ⟨L, cons true (cons true (cons true (cons true (cons true (R))))), .E⟩ := rfl
  exact steps_congr trans (a := 14) (by omega) (h0)

end H98843M
