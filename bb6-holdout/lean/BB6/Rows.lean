import BB6.Iter

/-!
# Rows of the round recurrence

The round recurrence composes the rules.  Its first two rows:

* gap meets marker, d ≡ 0 (mod 4): BOUNCE^(d/4) then SWAP;
* gap meets marker, d ≡ 2 (mod 4): BOUNCE^((d−2)/4) then MERGE;

where d is the number of stripe cells between the gap and the marker.  On the tape the gap is `0 0 0` with the head
on its last cell, preceded by the last stripe cell `1`, and followed by the stripe `(10)^n` (d = 2n), the marker
`1 1` and the `0` that starts the next stripe.  The two rows are stated for n = 2k and n = 2k + 1.
-/

namespace BB6

/-- The cell in front of `rep k [a, b] (cons a s)` is `a`, whatever k is. -/
theorem rep_head (k : Nat) (a b : Bool) (s : Tape) : rep k [a, b] (cons a s) = cons a (rep k [b, a] s) :=
  (rep_shift' a b k s).symm

/-- Gap meets marker across 4k stripe cells: k bounces, then a swap.  The marker ends just left of the gap, which
has moved 2k + 1 cells right; 6k² + 24k + 21 steps. -/
theorem gap_marker_swap (k : Nat) (L R : Tape) :
    steps (bounceSteps k 0 + 21)
        ⟨cons false (cons false (cons true L)), cons false (rep (2 * k) [true, false] (cons true (cons true (cons false R)))), .E⟩
      = some ⟨cons false (cons false (cons true (cons true (rep k [false, true] L)))),
              cons false (cons true (cons false (rep k [true, false] R))), .E⟩ := by
  have h₁ := bounce_iter k 0 (cons true L) R
  have e : 0 + 2 * k = 2 * k := by omega
  rw [e, rep_zero, rep_head k true false L] at h₁
  have h₂ := swap (rep k [false, true] L) (rep k [true, false] R)
  exact steps_seq h₁ h₂

/-- Gap meets marker across 4k + 2 stripe cells: k bounces, then a merge.  Gap and marker become a wall `0 0` and a
packet `1 1 1` heads left in state A; 6k² + 30k + 31 steps. -/
theorem gap_marker_merge (k : Nat) (L R : Tape) :
    steps (bounceSteps k 1 + 31)
        ⟨cons false (cons false (cons true L)), cons false (rep (2 * k + 1) [true, false] (cons true (cons true (cons false R)))), .E⟩
      = some ⟨rep k [false, true] L,
              cons true (cons true (cons true (cons false (cons true (cons false (cons false (cons true (cons false (rep k [true, false] R))))))))), .A⟩ := by
  have h₁ := bounce_iter k 1 (cons true L) R
  have e : 1 + 2 * k = 2 * k + 1 := by omega
  rw [e, rep_head k true false L] at h₁
  have h₂ := merge (rep k [false, true] L) (rep k [true, false] R)
  exact steps_seq h₁ h₂

theorem gap_marker_swap_steps (k : Nat) : bounceSteps k 0 + 21 = 6 * k * k + 24 * k + 21 := by
  rw [bounceSteps_eq]; omega

theorem gap_marker_merge_steps (k : Nat) : bounceSteps k 1 + 31 = 6 * k * k + 30 * k + 31 := by
  rw [bounceSteps_eq]; omega

end BB6
