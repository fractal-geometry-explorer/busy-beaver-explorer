import Rules

/-!
# The transfer loop, for any number of sweeps

`J x y L` is the junction `L 1 b^x 111 F> b^(y+1) 1` (b = 110, blank on the right, any wall `L 1` on the left).
One sweep (`sweep` of `Rules.lean`) takes it to `J (x - 2) (y + 3)`; by induction, `t` sweeps move `2t` copies of
b out of the left block and put `3t` into the right one.  This is the 3/2 of the map.
-/

namespace H3292

open TM

/-- The junction `L 1 b^x 111 F> b^(y+1) 1`, blank on the right. -/
def J (x y : Nat) (L : Tape) : Config :=
  ⟨app [true, true, true] (rep x [false, true, true] (cons true L)),
   rep (y + 1) [true, true, false] (cons true blank), .F⟩

theorem one_sweep (x y : Nat) (L : Tape) : steps (18 * y + 50) (J (x + 2) y L) = some (J x (y + 3) L) := by
  have h := sweep x y L
  have r := rep_rotate y [true, true] [false, true, true] [true, true, false] rfl
    (cons false (cons true (cons true (cons false (cons true blank)))))
  simp only [app_cons, app_nil] at r
  have e : cons true (cons true (cons false (cons true (cons true (cons false (cons true (cons true
      (rep y [false, true, true] (cons false (cons true (cons true (cons false (cons true blank)))))))))))))
      = rep (y + 3 + 1) [true, true, false] (cons true blank) := by
    rw [r]
    show app [true, true, false] (app [true, true, false] (rep y [true, true, false]
      (app [true, true, false] (app [true, true, false] (cons true blank))))) = _
    rw [rep_app_comm, rep_app_comm]
    rfl
  simp only [J, app_cons, app_nil]
  rw [← e]; exact h

/-- `t` sweeps. -/
theorem sweeps (L : Tape) : ∀ t x y, ∃ s, steps s (J (x + 2 * t) y L) = some (J x (y + 3 * t) L) := by
  intro t
  induction t with
  | zero => intro x y; exact ⟨0, rfl⟩
  | succ t ih =>
    intro x y
    obtain ⟨s, hs⟩ := ih x (y + 3)
    have h1 := one_sweep (x + 2 * t) y L
    rw [show x + 2 * t + 2 = x + 2 * (t + 1) by omega] at h1
    rw [show y + 3 + 3 * t = y + 3 * (t + 1) by omega] at hs
    exact ⟨_, steps_seq trans h1 hs⟩

end H3292
