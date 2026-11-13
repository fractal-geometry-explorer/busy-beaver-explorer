import Rules

/-!
# The sweeps of a phase of 1RB0RE_0LC1LE_0RD1LD_1RA1LF_1LC0RA_0LB---, chained

`sweep` (Rules.lean) eats four zeros and adds two `100` to the wall.  Here j sweeps are chained by induction: with
4j + 4 zeros left of `1 0 0 0`, the wall grows by 2j pairs and four zeros are left.  The left tape is written
nearest cell first, so the wall `(100)^n` read from the head is `rep n [false, false, true]`.  Written by hand.
-/

namespace H53125

open TM

theorem wall_two (n : Nat) (X : Tape) :
    cons false (cons false (cons true (cons false (rep n [false, true, false] (cons false (cons true X)))))) =
      rep (n + 2) [false, false, true] X := by
  have h : cons false (rep n [false, true, false] (cons false (cons true X))) =
      rep n [false, false, true] (cons false (cons false (cons true X))) :=
    rep_rotate n [false] [false, true, false] [false, false, true] rfl (cons false (cons true X))
  rw [h]
  show app [false, false, true] (rep n [false, false, true] (app [false, false, true] X)) = _
  rw [rep_app_comm]
  rfl

/-- j sweeps: 4j zeros are eaten and the wall gains 2j words `100`. -/
theorem sweeps (j n : Nat) (L : Tape) : ∃ s,
    steps s ⟨cons false (rep n [false, false, true] (cons false (cons false (cons false (cons true
      (rep (4 * j + 4) [false] L)))))), blank, .A⟩ =
    some ⟨cons false (rep (n + 2 * j) [false, false, true] (cons false (cons false (cons false (cons true
      (rep 4 [false] L)))))), blank, .A⟩ := by
  induction j generalizing n with
  | zero => exact ⟨0, rfl⟩
  | succ j ih =>
    have h1 := sweep n (rep (4 * j) [false] L)
    have e : cons false (cons false (cons false (cons false (rep (4 * j) [false] L)))) =
        rep (4 * j + 4) [false] L := by
      rw [show 4 * j + 4 = 4 + 4 * j by omega, rep_add]; rfl
    rw [wall_two, e] at h1
    obtain ⟨s, hs⟩ := ih (n + 2)
    rw [show n + 2 * (j + 1) = n + 2 + 2 * j by omega]
    have e2 : rep (4 * (j + 1) + 4) [false] L =
        cons false (cons false (cons false (cons false (rep (4 * j + 4) [false] L)))) := by
      rw [show 4 * (j + 1) + 4 = 4 + (4 * j + 4) by omega, rep_add]; rfl
    rw [e2]
    exact ⟨_, steps_seq trans h1 hs⟩

end H53125
