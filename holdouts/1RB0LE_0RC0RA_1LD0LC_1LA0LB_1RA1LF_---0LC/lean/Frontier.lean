import Left

/-!
# From blank tape through the first carry into the left end

Chaining the proved rules from blank tape:

1. `reach_s0` (Counter.lean, `native_decide`): after 59,129 steps, phase R with the digits `ds0` and a wall of 2 units.
   Read with the next unit of the left part as a 50th digit (`R0_eq`), this is a 50-unit counter left of `L_0`.
2. `up` counts it to all ones; `fe 0` carries into `L_0`; `up` counts again; … ; `fe 16`; `up` (`reach_L17`).
3. `s1`: the carry into `L_17` reaches the left end of the tape.  The wall has `2 p0 + 2` units then, with
   `p0 = 321,163,084,821,590,067,792,163`; it becomes the new counter `ds1 p0` of `2 p0 + 3` units, and the old counter
   the 24 blocks of `L1 = P (1^9 0 1 0)^24 Q` (`reach_S1`).
4. `up` counts the new counter to all ones, then `fo 0`, `up`, …, `fo 5`, `up` (`reach_jump`): the configuration just
   before the 7th carry into `L1`, the first one that crosses the blocks to `P`.

The new counter has `2^(3 p0 + 4)` values, so this takes more than `8^(p0+1)` steps: **no halt in the first
`8^(p0+1)` steps** (`no_halt_early`), a number with about 2.9·10^23 digits.

Everything here is checked by Lean's kernel, on top of `reach_s0` (compiled evaluation).
-/

namespace H136111

open TM

/-! ## The new counter -/

theorem d30_length : ∀ k : Nat, (d30 k).length = 2 * k
  | 0 => rfl
  | k + 1 => by simp [d30, d30_length k]; omega

theorem d30_valid : ∀ k : Nat, Valid false (d30 k)
  | 0 => trivial
  | k + 1 => ⟨by simp [cap], by simp [cap], d30_valid k⟩

theorem ds1_length (p : Nat) : (ds1 p).length = 2 * p + 3 := by
  simp [ds1, d30_length]; omega

theorem ds1_valid (p : Nat) : Valid true (ds1 p) := ⟨by simp [cap], d30_valid (p + 1)⟩

theorem capP_false_even : ∀ k : Nat, capP false (2 * k) = 8 ^ k
  | 0 => rfl
  | k + 1 => by
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
    simp only [capP, Bool.not_false, Bool.not_true]
    rw [capP_false_even k, Nat.pow_succ]; simp [cap]; omega

theorem capP_odd (k : Nat) : capP true (2 * k + 1) = 2 * 8 ^ k := by
  simp only [capP, Bool.not_true]; rw [capP_false_even]; simp [cap]

theorem val_d30 : ∀ k : Nat, 7 * val false (d30 k) + 3 = 3 * capP false (2 * k)
  | 0 => rfl
  | k + 1 => by
    have ih := val_d30 k
    have e1 : val false (d30 (k + 1)) = 3 + 4 * (0 + 2 * val false (d30 k)) := rfl
    have e2 : capP false (2 * (k + 1)) = 4 * (2 * capP false (2 * k)) := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega]; rfl
    rw [e1, e2]; omega

/-- The new counter is far from full: at least two below its maximum. -/
theorem ds1_room (p : Nat) : val true (ds1 p) + 2 ≤ capP true (2 * p + 3) := by
  have h := val_d30 (p + 1)
  have e1 : val true (ds1 p) = 1 + 2 * val false (d30 (p + 1)) := rfl
  have e2 : capP true (2 * p + 3) = 2 * capP false (2 * (p + 1)) := by
    rw [show 2 * p + 3 = 2 * (p + 1) + 1 by omega]; rfl
  have e3 : val false (d30 (p + 1)) = 3 + 4 * (0 + 2 * val false (d30 p)) := rfl
  rw [e1, e2]; omega

/-! ## Chains of carries and counts -/

/-- The 17 carries into `L_k`, each followed by a full count of the 50-unit counter. -/
theorem ev_chain : ∀ (r k n : Nat), k + r = 17 →
    ∃ t, steps t (R (top true 50) (n + 1) (Lt k)) =
      some (R (top true 50) (n + 1 + r * (capP true 50 - 1 + 1)) (Lt 17))
  | 0, k, n, h => ⟨0, by rw [show k = 17 by omega]; simp⟩
  | r + 1, k, n, h => by
    obtain ⟨t1, h1⟩ := fe k (by omega) 24 n
    obtain ⟨t2, -, h2⟩ := up 50 (bot true 50) (bot_length true 50) (valid_bot true 50) (n + 2) (Lt (k + 1))
    rw [val_bot] at h2
    obtain ⟨t3, h3⟩ := ev_chain r (k + 1) (n + 1 + (capP true 50 - 1 - 0)) (by omega)
    rw [show n + 2 + (capP true 50 - 1 - 0) = n + 1 + (capP true 50 - 1 - 0) + 1 by omega] at h2
    have e2 : n + 1 + (r + 1) * (capP true 50 - 1 + 1) =
        n + 1 + (capP true 50 - 1 - 0) + 1 + r * (capP true 50 - 1 + 1) := by
      have := Nat.add_one_mul r (capP true 50 - 1 + 1); omega
    rw [e2]
    exact ⟨t1 + (t2 + t3), steps_seq trans h1 (steps_seq trans h2 h3)⟩

/-- The first six carries into `L1` (they only change `Q`), each followed by a full count of the odd counter. -/
theorem od_chain (q : Nat) (PB : Tape) : ∀ (r k n : Nat), k + r = 6 →
    ∃ t, r * (capP true (2 * q + 3) - 1) ≤ t ∧
      steps t (R (top true (2 * q + 3)) (n + 1) (app (qk k) PB)) =
        some (R (top true (2 * q + 3)) (n + 1 + r * (capP true (2 * q + 3) - 1 + 1)) (app (qk 6) PB))
  | 0, k, n, h => ⟨0, by simp, by rw [show k = 6 by omega]; simp⟩
  | r + 1, k, n, h => by
    obtain ⟨t1, h1⟩ := fo k (by omega) q n PB
    obtain ⟨t2, ht2, h2⟩ := up (2 * q + 3) (bot true (2 * q + 3)) (bot_length true _) (valid_bot true _) (n + 2)
      (app (qk (k + 1)) PB)
    rw [val_bot] at h2 ht2
    obtain ⟨t3, ht3, h3⟩ := od_chain q PB r (k + 1) (n + 1 + (capP true (2 * q + 3) - 1 - 0)) (by omega)
    rw [show n + 2 + (capP true (2 * q + 3) - 1 - 0) = n + 1 + (capP true (2 * q + 3) - 1 - 0) + 1 by omega] at h2
    have e2 : n + 1 + (r + 1) * (capP true (2 * q + 3) - 1 + 1) =
        n + 1 + (capP true (2 * q + 3) - 1 - 0) + 1 + r * (capP true (2 * q + 3) - 1 + 1) := by
      have := Nat.add_one_mul r (capP true (2 * q + 3) - 1 + 1); omega
    rw [e2]
    have e3 := Nat.add_one_mul r (capP true (2 * q + 3) - 1)
    exact ⟨t1 + (t2 + t3), by omega, steps_seq trans h1 (steps_seq trans h2 h3)⟩

/-! ## The run from blank tape -/

/-- The wall at the carry into the left end has `2 p0 + 2` units. -/
def p0 : Nat := 321163084821590067792163

/-- The digits at step 59,129, with the next unit of `L0` read as a 50th digit (`Y3`). -/
def ds0' : List Nat := ds0 ++ [3]

theorem R0_eq : R ds0 2 L0 = R ds0' 2 (Lt 0) := by
  rw [ds0', R_snoc (show ds0.length = 49 by rfl)]
  rfl

/-- After 17 carries into the left part and 18 counts: all 50 units full, left of them `L_17`. -/
theorem reach_L17 : ∃ t, steps t init = some (R (top true 50) (2 * p0 + 2) (Lt 17)) := by
  obtain ⟨t1, -, h1⟩ := up 50 ds0' (by decide) (by simp [Valid, cap, ds0', ds0]) 2 (Lt 0)
  have hA : 2 + (capP true 50 - 1 - val true ds0') = (1 + (capP true 50 - 1 - val true ds0')) + 1 := by omega
  rw [hA] at h1
  obtain ⟨t2, h2⟩ := ev_chain 17 0 (1 + (capP true 50 - 1 - val true ds0')) rfl
  have hn : 1 + (capP true 50 - 1 - val true ds0') + 1 + 17 * (capP true 50 - 1 + 1) = 2 * p0 + 2 := by decide
  rw [hn] at h2
  have h0 := reach_s0
  rw [show s0.ds = ds0 from rfl, show s0.n = 2 from rfl, R0_eq] at h0
  exact ⟨59129 + (t1 + t2), steps_seq trans h0 (steps_seq trans h1 h2)⟩

/-- The carry into `L_17` reaches the left end: the wall becomes a counter of `2 p0 + 3` units. -/
theorem reach_S1 : ∃ t, steps t init = some (R (ds1 p0) 0 (L1t 24)) := by
  obtain ⟨t1, h1⟩ := reach_L17
  obtain ⟨t2, h2⟩ := s1 24 p0
  exact ⟨t1 + t2, steps_seq trans h1 h2⟩

/-- The blocks and `P` of `L1`. -/
def PB24 : Tape := rep 24 bB (app pP blank)

/-- The new counter counts up, and six carries into `Q` follow, each with a full count: the configuration just before
the 7th carry into `L1`.  It takes more than `6 (2^(3 p0 + 4) - 1)` steps. -/
theorem reach_jump : ∃ n t, 6 * (capP true (2 * p0 + 3) - 1) ≤ t ∧
    steps t init = some (R (top true (2 * p0 + 3)) n (app (qk 6) PB24)) := by
  obtain ⟨t1, h1⟩ := reach_S1
  have hroom := ds1_room p0
  obtain ⟨t2, -, h2⟩ := up (2 * p0 + 3) (ds1 p0) (ds1_length p0) (ds1_valid p0) 0 (L1t 24)
  have hb : 0 + (capP true (2 * p0 + 3) - 1 - val true (ds1 p0)) =
      (capP true (2 * p0 + 3) - 2 - val true (ds1 p0)) + 1 := by omega
  rw [hb, show L1t 24 = app (qk 0) PB24 from rfl] at h2
  obtain ⟨t3, ht3, h3⟩ := od_chain p0 PB24 6 0 _ rfl
  exact ⟨_, t1 + (t2 + t3), by omega, steps_seq trans h1 (steps_seq trans h2 h3)⟩

/-- **No halt in the first `8^(p0+1)` steps** (`p0 = 321,163,084,821,590,067,792,163`), a number with about
2.9·10^23 decimal digits. -/
theorem no_halt_early : ∀ t, t ≤ 8 ^ (p0 + 1) → ∃ c, steps t init = some c := by
  intro t ht
  obtain ⟨n, T, hT, h⟩ := reach_jump
  have hc : capP true (2 * p0 + 3) = 2 * 8 ^ (p0 + 1) := by
    rw [show 2 * p0 + 3 = 2 * (p0 + 1) + 1 by omega, capP_odd]
  rw [hc] at hT
  have hpos : 0 < 8 ^ (p0 + 1) := Nat.pow_pos (by decide)
  have e : T = t + (T - t) := by omega
  rw [e] at h
  exact steps_le trans h

end H136111
