import Reduction

/-!
# 1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE: a lower bound on the halting time

`go` iterates `F` and `T` together (tail recursion, so the kernel evaluates it in one pass); `go_eq` says it computes
`orbit` and `time`.  Evaluating `time 5000` (kernel) shows that if the machine halts at all, it takes more than
2^2073 steps; `time 200000` (compiled evaluation) gives 2^80181.
-/

namespace H31371

/-- `go n (x, t)`: n more samples from sample x reached at step t. -/
def go : Nat → (Nat × Nat) × Nat → (Nat × Nat) × Nat
  | 0, s => s
  | n + 1, (x, t) => go n (F x, t + T x)

theorem go_eq (n m : Nat) : go n (orbit m, time m) = (orbit (m + n), time (m + n)) := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    show go n (F (orbit m), time m + T (orbit m)) = _
    have := ih (m + 1)
    rw [show m + 1 + n = m + (n + 1) by omega] at this
    exact this

theorem time_eq (n : Nat) : time n = (go n ((0, 2), 7)).2 := by
  have := go_eq n 0
  rw [Nat.zero_add] at this
  rw [show ((0, 2), 7) = (orbit 0, time 0) from rfl, this]

/-- **If the machine halts from blank tape, it runs more than 2^2073 steps first** (kernel evaluation). -/
theorem halt_time_kernel {N : Nat} {c : Config} (hN : steps N init = some c) (hc : step c = none) :
    2 ^ 2073 < N := by
  have h := time_lt_of_halts hN hc 5000
  have e : 2 ^ 2073 ≤ (go 5000 ((0, 2), 7)).2 := by decide +kernel
  rw [time_eq] at h
  omega

/-- The same with 200,000 samples, by compiled evaluation (`native_decide`): more than 2^80181 steps. -/
theorem halt_time_native {N : Nat} {c : Config} (hN : steps N init = some c) (hc : step c = none) :
    2 ^ 80181 < N := by
  have h := time_lt_of_halts hN hc 200000
  have e : 2 ^ 80181 ≤ (go 200000 ((0, 2), 7)).2 := by native_decide
  rw [time_eq] at h
  omega

end H31371
