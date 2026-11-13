import Machine

/-! The two local rules of the tick, written by `bbtools.symtm.prove` (from `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/gen_clock.py`). -/

namespace H155590

open TM

/-- The sweep: `0 0 C> 1^(3+2n) 0` becomes `1 0^(4+2n) 1 A>`. -/
theorem rule_sweep (n : Nat) (L R : Tape) :
    steps (2 * n + 8) ⟨cons false (cons false (L)), cons true (rep (2 * n) [true] (cons true (cons true (cons false (R))))), .C⟩ = some ⟨cons true (cons false (cons false (rep (2 * n) [false] (cons false (cons false (cons true (L))))))), R, .A⟩ := by
  have h0 : steps 5 ⟨cons false (cons false (L)), cons true (rep (2 * n) [true] (cons true (cons true (cons false (R))))), .C⟩ = some ⟨cons false (cons false (cons true (L))), rep (2 * n) [true] (cons true (cons true (cons false (R)))), .D⟩ := rfl
  have c1 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .D⟩ = some ⟨app [] (app [false] L), R, .D⟩ := fun _ _ => rfl
  have h1 : steps ((2 * n) * 1) ⟨cons false (cons false (cons true (L))), rep (2 * n) [true] (cons true (cons true (cons false (R)))), .D⟩ = some ⟨rep (2 * n) [false] (cons false (cons false (cons true (L)))), cons true (cons true (cons false (R))), .D⟩ :=
    cross_r trans c1 (2 * n) (cons false (cons false (cons true (L)))) (cons true (cons true (cons false (R))))
  have h2 : steps 3 ⟨rep (2 * n) [false] (cons false (cons false (cons true (L)))), cons true (cons true (cons false (R))), .D⟩ = some ⟨cons true (cons false (cons false (rep (2 * n) [false] (cons false (cons false (cons true (L))))))), R, .A⟩ := rfl
  exact steps_congr trans (a := 5 + ((2 * n) * 1 + (3))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (h2)))

/-- The merge: `1 0 C> 1` becomes `C> 1 1 1`. -/
theorem rule_merge (L R : Tape) :
    steps (2) ⟨cons false (cons true (L)), cons true (R), .C⟩ = some ⟨L, cons true (cons true (cons true (R))), .C⟩ := by
  have h0 : steps 2 ⟨cons false (cons true (L)), cons true (R), .C⟩ = some ⟨L, cons true (cons true (cons true (R))), .C⟩ := rfl
  exact steps_congr trans (a := 2) (by omega) (h0)

end H155590
