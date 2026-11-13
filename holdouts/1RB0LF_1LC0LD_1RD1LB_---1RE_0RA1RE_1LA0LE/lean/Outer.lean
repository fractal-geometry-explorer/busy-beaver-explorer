import Reduce

/-!
# 1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE: the first phase of an epoch, and where it halts

An *outer configuration* is `O N = 1^N F>0 0 1^3` (the macro configuration `⟨N, 0, none, 0, some 0⟩`); the run from
blank tape passes through `O 10`, `O 27`, `O 60`, `O 118`, ... .  From `O N` the left block `X` is eaten by
*passes*: in a pass the right block `2q + 3` is used up in `q + 1` rounds (two 1s off `X` and off the block each
time, two new units), and then the units merge into the block `2(2q + 4) + 3 = 2(2q + 3) + 5`
(`pass`: `X ↦ X - (2q + 6)`, `q ↦ 2q + 4`).  The run halts if a pass ends with exactly four 1s on the left
(`pass_halt`).  Starting from `q = 0` that happens after `n` passes exactly when `N = 2^(n+4) - 2n - 10`
(`outer_halts`): `O 6`, `O 20`, `O 50`, `O 112`, `O 238`, `O 492`, ... halt.

Everything is checked by Lean's kernel.
-/

namespace H15252

open TM

/-- `q + 1` rounds against the tail `2q + 3`, from a left block of `x + 2(q + 1) + 1`. -/
theorem rounds_tail : ∀ (q a x : Nat), ∃ k,
    steps k (cfg ⟨x + 2 * (q + 1) + 1, a, .none, 0, some q⟩) = some (cfg ⟨x + 1, a + 2 * q + 3, .none, 0, none⟩)
  | 0, a, x => ⟨_, c_tail x a 0 0⟩
  | q + 1, a, x => by
    have h1 := c_tail (x + 2 * q + 2) a 0 (q + 1)
    obtain ⟨k, h2⟩ := rounds_tail q (a + 2) x
    simp only [tailNext, Nat.add_zero] at h1
    rw [show x + 2 * q + 2 + 1 = x + 2 * (q + 1) + 1 by omega] at h1
    rw [show x + 2 * (q + 1 + 1) + 1 = x + 2 * q + 2 + 3 by omega]
    rw [show a + 2 * (q + 1) + 3 = a + 2 + 2 * q + 3 by omega]
    exact ⟨_, steps_seq trans h1 h2⟩

/-- A pass: `X = x + 2q + 7` becomes `x + 1`, the tail `2q + 3` becomes `2(2q + 4) + 3`. -/
theorem pass (x q : Nat) : ∃ k,
    steps k (cfg ⟨x + 2 * q + 7, 0, .none, 0, some q⟩) = some (cfg ⟨x + 1, 0, .none, 0, some (2 * q + 4)⟩) := by
  obtain ⟨k, h1⟩ := rounds_tail q 0 (x + 4)
  have h2 := c_units5 x (0 + 2 * q + 3) 0
  rw [show x + 4 + 1 = x + 5 by omega] at h1
  rw [show x + 2 * q + 7 = x + 4 + 2 * (q + 1) + 1 by omega]
  rw [show 0 + 2 * q + 3 + 0 + 1 = 2 * q + 4 by omega] at h2
  exact ⟨_, steps_seq trans h1 h2⟩

/-- A pass that leaves exactly four 1s on the left halts. -/
theorem pass_halt (q : Nat) : Halts trans (cfg ⟨2 * q + 6, 0, .none, 0, some q⟩) := by
  obtain ⟨k, h1⟩ := rounds_tail q 0 3
  rw [show 3 + 2 * (q + 1) + 1 = 2 * q + 6 by omega] at h1
  obtain ⟨n, c, h2, hc⟩ := c_units4 (0 + 2 * q + 3) 0
  exact halts_of_steps h1 ⟨n, c, h2, hc⟩

/-- The left block from which the run halts after `n` more passes, the tail being `2q + 3`. -/
def T : Nat → Nat → Nat
  | 0, q => 2 * q + 6
  | n + 1, q => 2 * q + 6 + T n (2 * q + 4)

theorem halts_T : ∀ (n q : Nat), Halts trans (cfg ⟨T n q, 0, .none, 0, some q⟩)
  | 0, q => pass_halt q
  | n + 1, q => by
    have hT : 1 ≤ T n (2 * q + 4) := by cases n <;> simp [T] <;> omega
    obtain ⟨k, h⟩ := pass (T n (2 * q + 4) - 1) q
    rw [show T n (2 * q + 4) - 1 + 1 = T n (2 * q + 4) by omega,
      show T n (2 * q + 4) - 1 + 2 * q + 7 = T (n + 1) q by simp only [T]; omega] at h
    exact halts_of_steps h (halts_T n (2 * q + 4))

theorem T_closed : ∀ (n q : Nat), T n q + 2 * (n + 1) + 2 * (q + 4) = (q + 4) * 2 ^ (n + 2)
  | 0, q => by simp [T]; omega
  | n + 1, q => by
    have ih := T_closed n (2 * q + 4)
    simp only [T]
    rw [show 2 * q + 4 + 4 = 2 * (q + 4) by omega, Nat.mul_assoc] at ih
    rw [show n + 1 + 2 = n + 2 + 1 by omega, Nat.pow_succ, Nat.mul_comm (2 ^ (n + 2)) 2, Nat.mul_left_comm]
    generalize (q + 4) * 2 ^ (n + 2) = p at *
    omega

theorem T_zero (n : Nat) : T n 0 = 2 ^ (n + 4) - 2 * n - 10 := by
  have h := T_closed n 0
  have e : 2 ^ (n + 4) = 4 * 2 ^ (n + 2) := by
    rw [show n + 4 = (n + 2) + 2 by omega, Nat.pow_add]; omega
  omega

/-- **Halting outer configurations.**  `1^N F>0 0 1^3` halts when `N = 2^(n+4) - 2n - 10` (6, 20, 50, 112, 238, ...). -/
theorem outer_halts (n : Nat) : Halts trans (cfg ⟨2 ^ (n + 4) - 2 * n - 10, 0, .none, 0, some 0⟩) := by
  rw [← T_zero]; exact halts_T n 0

end H15252
