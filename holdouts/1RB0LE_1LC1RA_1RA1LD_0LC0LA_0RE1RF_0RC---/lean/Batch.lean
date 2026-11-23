import Criterion

/-!
# The two shortcuts of `c/fast.c`

`c/fast.c` runs the orbit of DeepMind's map with two shortcuts, both stated and proved here for `next` itself.

* `left_step`: from `C (3 q + r) k (q + 2 + c)` with `q ≥ 1`, `r < 3`, the map takes `q + 1` steps (`q` sweeps, then
  the small-left clause) to `C (4 q + 2 k + 2 + 2 [r = 1]) 1 c`.  The tables of `fast.c` are this formula composed
  `L` times (with `k = 1` after the first step); the program accepts a run of `L` steps only when the final right
  block is at least 101, which by `left_step` (applied step by step, `b` decreasing) is exactly the condition that
  every step in the run is a left step.
* `wall_step`: from `C (3 b + d) k b` the map takes `b + 1` steps (`b` sweeps, then the wall) to
  `C (d + 1) 0 (2 (k + 2 b) + 2)`.  `fast.c` uses it when `d > 101`, so no near miss is skipped.

Halting is decided by `halts_iff_visits` (`Criterion.lean`): a visit to `C (3 B + 1) k B`.  Neither shortcut
passes over a sweep start with `|m − 3 b − 1| ≤ 100` (left steps have `m − 3 b ≤ −4`, and both shortcuts demand a
margin of 101), so the program sees every candidate.
-/

set_option autoImplicit false

namespace H9516

open DM

theorem iter_succ' (j : Nat) (s : Option State) : iter (j + 1) s = Option.bind (iter j s) next := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih => show iter (j + 1) (Option.bind s next) = _; rw [ih]; rfl

/-- One left step: `q` sweeps, then the small-left clause. -/
theorem left_step (q r k c : Nat) (hq : 1 ≤ q) (hr : r < 3) :
    iter (q + 1) (some (.C (3 * q + r) k (q + 2 + c))) =
      some (.C (4 * q + 2 * k + 2 + (if r = 1 then 2 else 0)) 1 c) := by
  have h := sweep q r k (c + 2)
  rw [show r + 3 * q = 3 * q + r by omega, show c + 2 + q = q + 2 + c by omega] at h
  rw [iter_succ', h]
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 by omega) with rfl | rfl | rfl
  · rw [show k + 2 * (q + 1) = (k + 2 * q + 2) + 0 by omega]
    show some (State.C (2 * (k + 2 * q + 2) + 2) 1 c) = _
    simp only [show ((0 : Nat) = 1) = False by decide, ite_false]; congr 2; omega
  · rw [show k + 2 * (q + 1) = (k + 2 * q + 1) + 1 by omega]
    show some (State.C (2 * (k + 2 * q + 1) + 6) 1 c) = _
    simp only [ite_true]; congr 2; omega
  · rw [show k + 2 * (q + 1) = (k + 2 * q) + 2 by omega]
    show some (State.C (2 * (k + 2 * q) + 6) 1 c) = _
    simp only [show ((2 : Nat) = 1) = False by decide, ite_false]; congr 2; omega

/-- One wall step: `b` sweeps, then the wall. -/
theorem wall_step (b d k : Nat) :
    iter (b + 1) (some (.C (3 * b + d) k b)) = some (.C (d + 1) 0 (2 * (k + 2 * b) + 2)) := by
  have h := sweep b d k 0
  rw [show d + 3 * b = 3 * b + d by omega, show 0 + b = b by omega] at h
  rw [iter_succ', h]
  rfl

end H9516
