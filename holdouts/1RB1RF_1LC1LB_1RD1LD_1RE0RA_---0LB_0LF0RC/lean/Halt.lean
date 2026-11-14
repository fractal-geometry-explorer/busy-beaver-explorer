import Machine
import Rules
import Phase
import HaltRule

/-!
# 1RB1RF_1LC1LB_1RD1LD_1RE0RA_---0LB_0LF0RC: a halting criterion

Read the tape as the lengths of its runs of 1s. At a visit of the left end the tape is `3 2^n 3^p ...`; a *marker*
(a run of 5, or of 1) walks to the right through runs of 3, one run every two visits (`eat'`). If nothing but runs of
3 and the final run 1 lies behind the marker, the marker reaches the end of the tape and the machine halts:

* `halts_marker5`: `0^inf D> 0111011 (011)^n (1011)^p (1110)^(k+1) 1 0^inf` (run lengths `3 2^n 3^p 5 3^k 1`) halts;
* `halts_marker1`: `0^inf D> 0111011 (011)^n (1011)^p 1010 (1110)^k 1 0^inf` (run lengths `3 2^n 3^(p+1) 1 3^k 1`) halts,

for every n, p and k.  Whether the run from blank tape reaches such a configuration is open.
-/

namespace H279

open TM

theorem halts_marker5 (n p k : Nat) : TM.Halts trans (Y n p (dk (k + 1) blank)) := by
  have h1 := eats k n p 0 blank
  rw [show 0 + 1 + k = k + 1 by omega] at h1
  have h2 := tail (n + 2 * k) (p + k)
  have h2' : steps (25 * (n + 2 * k) + 24 * (p + k) + 120) (Y (n + 2 * k) (p + k) (dk (0 + 1) blank)) = _ := h2
  exact ⟨_, _, steps_seq trans h1 h2', rfl⟩

theorem halts_marker1 (n p k : Nat) :
    TM.Halts trans (Y n p (cons true (cons false (cons true (cons false (dk k blank)))))) := by
  cases k with
  | zero => exact ⟨_, _, tail2 n p, rfl⟩
  | succ k =>
    have h1 : steps (10 * n + 10 * p + 41) (Y n p (cons true (cons false (cons true (cons false (dk (k + 1) blank))))))
        = some (Y (n + 1) (p + 1) (dk (k + 1) blank)) := by
      have h := marker1 n p (dk k blank)
      rw [rot] at h
      unfold Y
      rw [rep_add p 1]
      exact h
    obtain ⟨a, c, h2, h3⟩ := halts_marker5 (n + 1) (p + 1) k
    exact ⟨_, c, steps_seq trans h1 h2, h3⟩

end H279
