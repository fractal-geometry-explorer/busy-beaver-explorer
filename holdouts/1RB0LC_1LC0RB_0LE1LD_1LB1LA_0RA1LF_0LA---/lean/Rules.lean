import Machine

/-! The two local rules of the tick, written by `bbtools.symtm.prove` (from `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/gen_clock.py`). -/

namespace H74449

open TM

/-- The sweep: `0 0 0 D> 0 1^(3+3n) 0` becomes `0 1 0^(5+3n) B> 0`. -/
theorem rule_sweep (n : Nat) (L R : Tape) :
    steps (3 * n + 10) ⟨cons false (cons false (cons false (L))), cons false (rep (3 * n) [true] (cons true (cons true (cons true (cons false (R)))))), .D⟩ = some ⟨cons false (cons false (cons false (rep (3 * n) [false] (cons false (cons false (cons true (cons false (L)))))))), cons false (R), .B⟩ := by
  have h0 : steps 7 ⟨cons false (cons false (cons false (L))), cons false (rep (3 * n) [true] (cons true (cons true (cons true (cons false (R)))))), .D⟩ = some ⟨cons false (cons false (cons true (cons false (L)))), rep (3 * n) [true] (cons true (cons true (cons true (cons false (R))))), .B⟩ := rfl
  have c1 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .B⟩ = some ⟨app [] (app [false] L), R, .B⟩ := fun _ _ => rfl
  have h1 : steps ((3 * n) * 1) ⟨cons false (cons false (cons true (cons false (L)))), rep (3 * n) [true] (cons true (cons true (cons true (cons false (R))))), .B⟩ = some ⟨rep (3 * n) [false] (cons false (cons false (cons true (cons false (L))))), cons true (cons true (cons true (cons false (R)))), .B⟩ :=
    cross_r trans c1 (3 * n) (cons false (cons false (cons true (cons false (L))))) (cons true (cons true (cons true (cons false (R)))))
  have h2 : steps 3 ⟨rep (3 * n) [false] (cons false (cons false (cons true (cons false (L))))), cons true (cons true (cons true (cons false (R)))), .B⟩ = some ⟨cons false (cons false (cons false (rep (3 * n) [false] (cons false (cons false (cons true (cons false (L)))))))), cons false (R), .B⟩ := rfl
  exact steps_congr trans (a := 7 + ((3 * n) * 1 + (3))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (h2)))

/-- The merge: `0 1 0 D> 0` becomes `D> 0 1 1 1`. -/
theorem rule_merge (L R : Tape) :
    steps (3) ⟨cons false (cons true (cons false (L))), cons false (R), .D⟩ = some ⟨L, cons false (cons true (cons true (cons true (R)))), .D⟩ := by
  have h0 : steps 3 ⟨cons false (cons true (cons false (L))), cons false (R), .D⟩ = some ⟨L, cons false (cons true (cons true (cons true (R)))), .D⟩ := rfl
  exact steps_congr trans (a := 3) (by omega) (h0)

end H74449
