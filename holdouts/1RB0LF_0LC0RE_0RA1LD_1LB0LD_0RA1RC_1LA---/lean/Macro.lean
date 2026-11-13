import Machine
import Gadgets

/-!
# 1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---: the short sweep

At the left records (state B on a new leftmost cell) the tape is `B>0 (10)^n0 h (10)^d0 s1 (10)^d1 s2 ...` with
head separator h either `1 0^3` or `1^2 0 1^2 0`, and separators `s = 1^2 0` (a digit 1) or `1 0^2` (a digit 0),
least significant first: a binary counter.  A long sweep (not in Lean) runs over the whole tape, increments the
counter and takes 2 from n0; the short sweep that follows (`short`, 12x + 36 steps, n0 = 2x + 4) only turns
`1 0^3` back into `1^2 0 1^2 0`, for every tape R to its right.  `reach2438` puts the run from blank tape in this
form.  Kernel only.
-/

namespace H129771

open TM

/-- The short sweep: `B>0 (10)^(2x+4) 1 0 0 0 R` becomes `B>0 (10)^(2x+4) 1 1 0 1 1 0 R`, two cells further left. -/
theorem short (x : Nat) (R : Tape) :
    steps (12 * x + 36) ⟨blank, cons false (rep (x + 2) [true, false, true, false] (cons true (cons false (cons false
      (cons false R))))), .B⟩ =
      some ⟨blank, cons false (rep (x + 2) [true, false, true, false] (cons true (cons true (cons false (cons true
      (cons true (cons false R))))))), .B⟩ := by
  have h := short_raw x R
  have e : cons true (cons false (cons true (rep (x + 1) [false, true, false, true] (cons false (cons true (cons true
      (cons false (cons true (cons true (cons false R)))))))))) =
      rep (x + 2) [true, false, true, false] (cons true (cons true (cons false (cons true (cons true
      (cons false R)))))) := by
    show app [true, false] (app [true] (rep (x + 1) [false, true, false, true] (app [false]
      (cons true (cons true (cons false (cons true (cons true (cons false R))))))))) = _
    rw [rep_rotate (x + 1) [true] [false, true, false, true] [true, false, true, false] rfl,
      rep_rotate (x + 1) [true, false] [true, false, true, false] [true, false, true, false] rfl]
    exact rep_app_comm (x + 1) [true, false, true, false] _
  rw [e] at h
  exact h

/-- The tape right of the counter's head separator at step 2438 (as the list simulator leaves it). -/
def R2438 : Tape := app [true, false, true, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, false, true, false, true, false, true, false, true, true, false] blank

/-- The list configuration at step 2438 (kernel evaluation): `B>0 (10)^12 1 0 0 0 R2438`. -/
theorem fsteps2438 : fsteps 2438 (FCfg.blank .A) = some ⟨[], [false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, true, false, true, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, false, true, false, true, false, true, false, true, true, false], .B⟩ := by
  decide +kernel

/-- From blank tape the run is at a short-sweep record after 2438 steps (n0 = 12, so x = 4). -/
theorem reach2438 : steps 2438 init =
    some ⟨blank, cons false (rep 6 [true, false, true, false] (cons true (cons false (cons false (cons false R2438))))), .B⟩ := by
  have h := blank_reaches trans fsteps2438
  exact h

/-- ... and 84 steps later at the next left record, by `short`. -/
theorem reach2522 : steps 2522 init =
    some ⟨blank, cons false (rep 6 [true, false, true, false] (cons true (cons true (cons false (cons true (cons true
      (cons false R2438))))))), .B⟩ :=
  steps_congr trans (a := 2438 + (12 * 4 + 36)) rfl (steps_seq trans reach2438 (short 4 R2438))

end H129771
