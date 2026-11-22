import Phases

/-!
# 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE: the sweep, many frames at once

Almost every frame of the run is one of the two cases `e l (j + 2) (r + 2)` and `h l (m + 1) (r + 2)` of `next`;
together they send `e L J R` to `e (L + 2) (J - 1) (R - 2)` in two frames.  `sweep` iterates that pair `k` times in
one statement.  `c/framemap.c` jumps over whole sweeps with it (and so iterates exactly the map `next`, whose
orbit decides halting by `halts_iff`); its machine-step count for the jump, `k (4J + 6) - 2k(k - 1)`, is the sum of
the two cases' step counts `2J + 7` and `2J - 1` from `Pieces.lean`.
-/

namespace H151878

theorem iter_add (a b : Nat) (p : Ph) : iter (a + b) p = (iter a p).bind (iter b) := by
  induction a generalizing p with
  | zero => simp [iter]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [iter]
    cases next p with
    | none => rfl
    | some q => simp only [Option.bind_some]; exact ih q

/-- One sweep step: two frames. -/
theorem sweep_one (L J R : Nat) : iter 2 (Ph.e L (J + 2) (R + 3)) = some (Ph.e (L + 2) (J + 1) (R + 1)) := by
  rfl

/-- `k` sweep steps: `2k` frames from `e L (J + 1 + k) (R + 1 + 2k)` to `e (L + 2k) (J + 1) (R + 1)`. -/
theorem sweep (k : Nat) : ∀ L J R : Nat,
    iter (2 * k) (Ph.e L (J + 1 + k) (R + 1 + 2 * k)) = some (Ph.e (L + 2 * k) (J + 1) (R + 1)) := by
  induction k with
  | zero => intro L J R; rfl
  | succ k ih =>
    intro L J R
    rw [show J + 1 + (k + 1) = (J + k) + 2 by omega, show R + 1 + 2 * (k + 1) = (R + 2 * k) + 3 by omega,
      show 2 * (k + 1) = 2 + 2 * k by omega, iter_add, sweep_one]
    simp only [Option.bind_some]
    rw [show J + k + 1 = J + 1 + k by omega, show R + 2 * k + 1 = R + 1 + 2 * k by omega, ih]
    congr 2; omega

end H151878
