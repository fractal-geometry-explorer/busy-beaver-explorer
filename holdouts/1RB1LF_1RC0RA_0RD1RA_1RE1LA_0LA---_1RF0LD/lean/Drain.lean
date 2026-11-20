import Dec

/-!
# 1RB1LF_1RC0RA_0RD1RA_1RE1LA_0LA---_1RF0LD: many decrements at once

The bit list of `Dec.lean` is a binary counter, lowest bit first.  Counting down `n` times from a value whose lowest
bit is `b`, the lowest bit is set at `nOdd b n` of the decrements (those take a copy from the first block) and clear
at the other `nEven b n`, which are exactly the decrements of the rest of the list.  So `n` decrements in a row are
one recursion over the list (`drainL`), with no loop over `n` (`dec1_drainL`: one more decrement is `drainL` with
`n + 1`).  `regN bl n` says that all `n` decrements are regular (`reg` of `Dec.lean` at each of them), again by one
recursion over the list, and `maxReg` is the largest such `n`.

`drain_reach`: `n` regular decrements in a row take at least `n (6 X + 6 n + 4)` steps (each takes
`6 X' + 6 zsum + 10` with `X' = X + 2 t` at the `t`-th, and `zsum` is dropped).
-/

namespace H180268

open TM

def nOdd (b : Bool) (n : Nat) : Nat := if b then (n + 1) / 2 else n / 2
def nEven (b : Bool) (n : Nat) : Nat := n - nOdd b n

/-- The bit list after `n` decrements. -/
def drainL : List (Bool × Nat) → Nat → List (Bool × Nat)
  | [], _ => []
  | (b, y) :: bl, n => (b != (n % 2 == 1), y - nOdd b n) :: drainL bl (nEven b n)

/-- All of the first `n` decrements are regular. -/
def regN : List (Bool × Nat) → Nat → Bool
  | _, 0 => true
  | [], _ + 1 => false
  | (b, y) :: bl, n + 1 => decide (nOdd b n + 1 ≤ y) && regN bl (nEven b (n + 1))

theorem drainL_zero : ∀ bl : List (Bool × Nat), drainL bl 0 = bl
  | [] => rfl
  | (b, y) :: bl => by
    simp only [drainL, nOdd, nEven]
    rw [show (if b = true then (0 + 1) / 2 else 0 / 2) = 0 by split <;> rfl]
    simp only [Nat.sub_zero, Nat.zero_mod]
    rw [drainL_zero bl]
    cases b <;> rfl

theorem regN_succ : ∀ (bl : List (Bool × Nat)) (n : Nat), regN bl (n + 1) = true →
    reg (drainL bl n) = true ∧ regN bl n = true ∧ dec1 (drainL bl n) = drainL bl (n + 1)
  | [], n, h => by simp [regN] at h
  | (b, y) :: bl, n, h => by
    simp only [regN, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    cases hb : (b != (n % 2 == 1)) with
    | true =>
      -- the next decrement is odd: the rest is untouched
      have ho : nOdd b (n + 1) = nOdd b n + 1 ∧ nEven b (n + 1) = nEven b n := by
        cases b <;> simp at hb <;> simp only [nOdd, nEven] <;> simp <;> omega
      refine ⟨?_, ?_, ?_⟩
      · simp only [drainL, hb, reg, decide_eq_true_eq]; omega
      · cases n with
        | zero => rfl
        | succ m =>
          simp only [regN, Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨?_, by rw [← ho.2]; exact h2⟩
          have : nOdd b m ≤ nOdd b (m + 1) := by cases b <;> simp only [nOdd] <;> simp <;> omega
          omega
      · simp only [drainL, hb, dec1, ho.1, ho.2]
        have e : (b != ((n + 1) % 2 == 1)) = false := by
          cases b <;> simp at hb ⊢ <;> omega
        rw [e, Nat.sub_add_eq]
    | false =>
      have ho : nOdd b (n + 1) = nOdd b n ∧ nEven b (n + 1) = nEven b n + 1 := by
        cases b <;> simp at hb <;> simp only [nOdd, nEven] <;> simp <;> omega
      rw [ho.2] at h2
      obtain ⟨r1, r2, r3⟩ := regN_succ bl (nEven b n) h2
      refine ⟨?_, ?_, ?_⟩
      · simp only [drainL, hb, reg, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by omega, r1⟩
      · cases n with
        | zero => rfl
        | succ m =>
          simp only [regN, Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨?_, r2⟩
          have : nOdd b m ≤ nOdd b (m + 1) := by cases b <;> simp only [nOdd] <;> simp <;> omega
          omega
      · simp only [drainL, hb, dec1, ho.1, ho.2, r3]
        have e : (b != ((n + 1) % 2 == 1)) = true := by
          cases b <;> simp at hb ⊢ <;> omega
        rw [e]

/-- The step bound in closed form. -/
def lowN (n X : Nat) : Nat := n * (6 * X + 6 * n + 4)

theorem lowN_succ (n X : Nat) : lowN (n + 1) X = lowN n X + (6 * (X + 2 * n) + 10) := by
  unfold lowN
  rw [show 6 * X + 6 * (n + 1) + 4 = (6 * X + 6 * n + 4) + 6 by omega, Nat.succ_mul, Nat.mul_add]
  omega

/-- **`n` regular decrements in a row**, in at least `lowN n X` steps. -/
theorem drain_reach (X : Nat) (bl : List (Bool × Nat)) (R : Tape) : ∀ n, regN bl n = true →
    ReachGe trans (event X bl R) (event (X + 2 * n) (drainL bl n) R) (lowN n X)
  | 0, _ => by rw [drainL_zero, Nat.mul_zero, Nat.add_zero]; exact (ReachGe.refl trans _).mono trans (by simp [lowN])
  | n + 1, h => by
    obtain ⟨r1, r2, r3⟩ := regN_succ bl n h
    have h1 := drain_reach X bl R n r2
    have h2 := dec_step (X + 2 * n) (drainL bl n) R r1
    rw [r3, show X + 2 * n + 2 = X + 2 * (n + 1) by omega] at h2
    rw [lowN_succ]
    exact (h1.trans trans (ReachGe.of_steps trans h2)).mono trans (by omega)

/-- The largest `n` with `regN bl n` (the test `regN bl (maxReg bl)` is what the jump relies on). -/
def maxReg : List (Bool × Nat) → Nat
  | [] => 0
  | (b, y) :: bl =>
    if y = 0 then 0 else
    let m := maxReg bl
    let b1 := (if b then 2 * (y - 1) else 2 * (y - 1) + 1) + 1
    let b2 := if b then 2 * m + 1 else 2 * m
    min b1 b2

end H180268
