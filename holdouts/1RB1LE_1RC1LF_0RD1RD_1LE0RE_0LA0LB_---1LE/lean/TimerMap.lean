/-!
# The timer map of 1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE (24 November 2026)

At an overflow (a right-end visit) the mirrored digit model of this machine (`py/digits.py`) reads
`W0 W0 ([T 1] W2 [0] W0) ([T 2] W2 [0] W0) ...`: a list of *timers* `T k`, each a run of `110` words.
Between two overflows, while no timer runs out, timer `k` loses `dec k` words: 3 for the top timer and
`2 * 4^(k-1)` below it (9, 24, 96, 384 ... cells, the README's right-end map).  This was read off an exact
full-state cycle of the condition-macro engine at 5.71e90 steps (all 75 timers), so the map itself is a computed
fact, not proved here.

When the top timer runs out with residue 0 (it goes 3 -> 0), the next overflow drops it and every timer
moves up one level, losing `6 * 4^(k-1) - 2` words in that cycle (seen in both long runs, near cycle 378,000).

This file proves the arithmetic that the README uses: `K` translation cycles at once, the run-out cycle of a
timer, and the fact that a translation cycle keeps the top timer's residue mod 3 (so the residue at the next
run-out is the residue now).
-/

namespace H99198.TimerMap

/-- Words of `110` that timer `k` (top = 1) loses per overflow cycle. -/
def dec : Nat → Nat
  | 0 => 0
  | 1 => 3
  | k + 2 => 2 * 4 ^ (k + 1)

theorem dec_values : dec 1 = 3 ∧ dec 2 = 8 ∧ dec 3 = 32 ∧ dec 4 = 128 ∧ dec 5 = 512 := by decide

/-- One translation cycle on a list of timers (head = top timer, level `k`). -/
def cycleFrom : Nat → List Nat → List Nat
  | _, [] => []
  | k, t :: ts => (t - dec k) :: cycleFrom (k + 1) ts

/-- One translation cycle, top timer at level 1. -/
def step (ts : List Nat) : List Nat := cycleFrom 1 ts

/-- `K` cycles at once: every timer loses `K * dec k`. -/
def jumpFrom : Nat → Nat → List Nat → List Nat
  | _, _, [] => []
  | K, k, t :: ts => (t - K * dec k) :: jumpFrom K (k + 1) ts

/-- `f` applied `K` times. -/
def iter (f : α → α) : Nat → α → α
  | 0, x => x
  | K + 1, x => f (iter f K x)

theorem cycle_jump_succ (K : Nat) : ∀ (k : Nat) (ts : List Nat),
    cycleFrom k (jumpFrom K k ts) = jumpFrom (K + 1) k ts
  | _, [] => rfl
  | k, t :: ts => by
      simp only [jumpFrom, cycleFrom, cycle_jump_succ K (k + 1) ts, Nat.sub_sub, Nat.succ_mul]

theorem jump_zero : ∀ (k : Nat) (ts : List Nat), jumpFrom 0 k ts = ts
  | _, [] => rfl
  | k, t :: ts => by simp only [jumpFrom, Nat.zero_mul, Nat.sub_zero, jump_zero (k + 1) ts]

/-- `K` translation cycles equal one jump by `K` (the jump used by the forecast runs). -/
theorem step_iter (ts : List Nat) : ∀ K : Nat, iter step K ts = jumpFrom K 1 ts
  | 0 => (jump_zero 1 ts).symm
  | K + 1 => by
      simp only [iter, step_iter ts K, step]
      exact cycle_jump_succ K 1 ts

/-- A translation cycle keeps the top timer's residue mod 3 while it is at least 3. -/
theorem top_residue (t : Nat) (h : 3 ≤ t) : (t - dec 1) % 3 = t % 3 := by
  simp only [dec]; omega

/-- So the top timer runs out (falls below 3) with the residue it has now, after `t / 3` cycles. -/
theorem top_runout (t K : Nat) (hK : K = t / 3) : t - K * dec 1 = t % 3 := by
  simp only [dec]; subst hK; omega

/-! ## The two long runs (forecast logs, 24 November 2026)

After their first top collapse (log cycle about 378,000; both at residue 0):
start A (blank tape, from 5.71e90 steps) had top timer 8,170,395 at log cycle 380,960, start B (the twin's
question, from 3.10e89 steps) had 8,144,300 at log cycle 389,559.  Timer 2 (38,953,792 and 38,883,928 words,
-8 per cycle) outlives timer 1, so the next run-out comes with today's residue: 0 for A, 2 for B.  That is what
the runs showed near log cycle 1,107,000 (A: 3 -> 0; B: 5 -> 2, after which timers 1 and 2 are both used up).

At log cycle 3,300,000: A has top timers 16,587,577 and 2,399,645,476, B has 2,331,944,982 and
26,154,194,953.  So A's third run-out comes with residue 1, after about 5.53 million more cycles. -/

theorem A_second_runout : 8170395 % 3 = 0 ∧ 8170395 / 3 = 2723465 ∧ 2723465 < 38953792 / 8 := by decide
theorem B_second_runout : 8144300 % 3 = 2 ∧ 8144300 / 3 = 2714766 ∧ 2714766 < 38883928 / 8 := by decide
theorem A_third_runout : 16587577 % 3 = 1 ∧ 16587577 / 3 = 5529192 ∧ 5529192 < 2399645476 / 8 := by decide
theorem B_third_runout : 2331944982 % 3 = 0 ∧ 2331944982 / 3 = 777314994 ∧ 777314994 < 26154194953 / 8 := by decide

end H99198.TimerMap
