import Machine
import Gadgets

/-!
# 1RB0LE_1RC0RF_0RD0RB_1RE0RC_1LA0LA_1RA---: the fill sweeps

Each cycle of the run starts from an E-record `P 1^3 0^K 1 E>0` (P a short prefix, K about doubling per cycle).
Then the gap `0^K` is filled from its right end: at the E-records

    fcfg z m L :   L 0^z 1 0 1 1 1 0 (10)^m 1 E>0     (blank tape to the right)

one sweep takes four 0s and gives four more `10` pairs (`fill`, 4m + 40 steps), and k sweeps at once (`fills`).
When fewer than four 0s are left, one pass to the left end and one back rewrite the prefix and open the next,
about twice as long, gap; those passes are not in Lean.  `reach3224` puts the run from blank tape in this form
(K = 99, cycle 5), and `reach_fill_end` follows it through the 23 sweeps of that gap.  Kernel only.
-/

namespace H70977

open TM

/-- The fill-phase E-record `L 0^z 1 0 1 1 1 0 (10)^m 1 E>0` (left tape nearest first). -/
def fcfg (z m : Nat) (L : Tape) : Config :=
  ⟨cons true (rep m [false, true] (cons false (cons true (cons true (cons true (cons false (cons true
    (rep z [false] L)))))))), blank, .E⟩

/-- One fill sweep. -/
theorem fill (z m : Nat) (L : Tape) : steps (4 * m + 40) (fcfg (z + 4) m L) = some (fcfg z (m + 4) L) := by
  have h := fill_raw m z L
  have e : cons true (cons false (cons true (cons false (rep m [true, false] (cons true (cons false (cons true
      (cons false (cons true (cons false (cons true (cons true (cons true (cons false (cons true
      (rep z [false] L)))))))))))))))) =
      cons true (rep (m + 4) [false, true] (cons false (cons true (cons true (cons true (cons false (cons true
      (rep z [false] L)))))))) := by
    show cons true (app [false] (rep 1 [true, false] (rep m [true, false] (rep 3 [true, false]
      (cons true (cons true (cons true (cons false (cons true (rep z [false] L)))))))))) = _
    rw [← rep_add, ← rep_add, rep_rotate _ [false] [true, false] [false, true] rfl,
      show 1 + m + 3 = m + 4 by omega]
    rfl
  rw [e] at h
  exact h

/-- The cost of k fill sweeps starting with m pairs. -/
def fcost : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, m => 4 * m + 40 + fcost k (m + 4)

/-- For example 23 sweeps from 2 pairs (the closed form is `k (4m + 40) + 8k(k - 1)`). -/
theorem fcost_23 : fcost 23 2 = 5152 := by decide

/-- k fill sweeps at once. -/
theorem fills (k z m : Nat) (L : Tape) :
    steps (fcost k m) (fcfg (z + 4 * k) m L) = some (fcfg z (m + 4 * k) L) := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    have h1 := fill (z + 4 * k) m L
    rw [show z + 4 * k + 4 = z + 4 * (k + 1) by omega] at h1
    have h2 := ih (m + 4)
    rw [show m + 4 + 4 * k = m + 4 * (k + 1) by omega] at h2
    exact steps_seq trans h1 h2

/-- The prefix left of the gap in cycle 5 (step 3194 to 3700). -/
def P5 : Tape := cons true (cons true (cons true (cons false (cons true (cons true (cons true (cons false (cons true (cons true (cons true (cons false (cons true (cons true (cons true (cons false (cons true (cons false (cons false (cons false (cons true (cons true (cons true (cons false (cons false (cons false (cons true (cons true (cons true (cons false (cons false (cons false (cons true (cons true (blank))))))))))))))))))))))))))))))))))

/-- The list configuration at step 3224 from blank tape (kernel evaluation). -/
theorem fsteps3224 : fsteps 3224 (FCfg.blank .A) = some ⟨[true, false, true, false, true, false, true, true, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, false, false, false, true, true, true, false, false, false, true, true, true, false, false, false, true, true], [], .E⟩ := by
  decide +kernel

/-- From blank tape the run is at the fill record `P5 0^95 1 0 1 1 1 0 (10)^2 1 E>0` after 3224 steps. -/
theorem reach3224 : steps 3224 init = some (fcfg 95 2 P5) := by
  have h := blank_reaches trans fsteps3224
  exact h

/-- ... and 23 fill sweeps later at `P5 0^3 1 0 1 1 1 0 (10)^94 1 E>0`. -/
theorem reach_fill_end : steps (3224 + fcost 23 2) init = some (fcfg 3 94 P5) :=
  steps_seq trans reach3224 (fills 23 3 2 P5)

end H70977
