import Phases

/-!
# 1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE: the fatal all-ones lengths, for every n

`Phases.lean` checks by `native_decide`, for `n < 100000`, which all-ones tapes `PR 0 n` halt before the next even
phase or all-ones tape.  Here that is proved for every `n`, by the kernel.  `PR 0 n` goes to `PE 1 (n+1)`.  From
`PE x z` with `z` odd the run is a chain of doublings `PE x z → PE (2x+4) (z-2x-6)`, which halts exactly when
`z = zHalt x k` for some `k`; at `z = 2x+5` (`z = zB x k` along the chain) it leaves the chain for `PE 1 (4x'+7)`,
where `x'` is the current `x` (`e_out`, by strong induction on `z`).  From `PE 1 1` the chain has
`x' = 5·2^k - 4`, and `PE 1 (20·2^k - 9)` is neither a halting value nor a branch value of the chain
(`branch_not_halt`, `branch_not_branch`), so it is safe.  With `zHalt 1 k = 10·2^k - 2k - 9` (`zHalt_closed`),
`PR 0 n` is fatal iff `n = 0` or `n = 20·2^k - 2k - 12` (`Fatal`, `ones_fate`, `ones_fatal_all`, `ones_safe_all`).
-/

namespace H70028

open TM

/-- The `z` values from which `PE x z` halts before an even phase or an all-ones tape. -/
def zHalt : Nat → Nat → Nat
  | _, 0 => 1
  | x, k + 1 => zHalt (2 * x + 4) k + 2 * x + 6

/-- The `z` values from which `PE x z` leaves the doubling chain for `PE 1 (4 * X x k + 7)`. -/
def zB : Nat → Nat → Nat
  | x, 0 => 2 * x + 5
  | x, k + 1 => zB (2 * x + 4) k + 2 * x + 6

/-- The `x` of the chain after `k` doublings. -/
def X : Nat → Nat → Nat
  | x, 0 => x
  | x, k + 1 => X (2 * x + 4) k

theorem zHalt_closed : ∀ k x, zHalt x k + 2 * k + 2 * (x + 4) = (x + 4) * 2 ^ (k + 1) + 1
  | 0, x => by simp [zHalt]; omega
  | k + 1, x => by
    have ih := zHalt_closed k (2 * x + 4)
    simp only [zHalt]
    rw [show 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) by rw [Nat.pow_succ, Nat.mul_comm]]
    rw [show 2 * x + 4 + 4 = 2 * (x + 4) by omega, Nat.mul_assoc] at ih
    rw [Nat.mul_left_comm]
    generalize (x + 4) * 2 ^ (k + 1) = A at *
    omega

theorem zB_closed : ∀ k x, zB x k + 2 * k + 2 * (x + 4) + 3 = (x + 4) * 2 ^ (k + 2)
  | 0, x => by simp [zB]; omega
  | k + 1, x => by
    have ih := zB_closed k (2 * x + 4)
    simp only [zB]
    rw [show 2 ^ (k + 1 + 2) = 2 * 2 ^ (k + 2) by rw [show k + 1 + 2 = (k + 2) + 1 by omega, Nat.pow_succ, Nat.mul_comm]]
    rw [show 2 * x + 4 + 4 = 2 * (x + 4) by omega, Nat.mul_assoc] at ih
    rw [Nat.mul_left_comm]
    generalize (x + 4) * 2 ^ (k + 2) = A at *
    omega

theorem X_closed : ∀ k x, X x k + 4 = (x + 4) * 2 ^ k
  | 0, x => by simp [X]
  | k + 1, x => by
    have ih := X_closed k (2 * x + 4)
    simp only [X]
    rw [ih, Nat.pow_succ, show 2 * x + 4 + 4 = 2 * (x + 4) by omega]
    rw [Nat.mul_comm (2 ^ k) 2, ← Nat.mul_assoc, Nat.mul_comm (x + 4) 2]

theorem zHalt_ge : ∀ k x, k ≥ 1 → zHalt x k ≥ 2 * x + 7
  | 0, _, h => absurd h (by omega)
  | k + 1, x, _ => by simp only [zHalt]; have : zHalt (2 * x + 4) k ≥ 1 := by
                                            cases k <;> simp [zHalt] <;> omega
                      omega

theorem fate_some (f : Nat) (p q : Ph) (hp : next p = some q) (hq : (isEven q || isOnes q) = true) :
    fate (f + 1) p = some false := by simp [fate, hp, hq]

theorem fate_step (p q : Ph) (hp : next p = some q) (hq : (isEven q || isOnes q) = false) (g : Nat) :
    fate (g + 1) p = fate g q := by simp [fate, hp, hq]

/-- What the run from `p` does, for a start `PE x z`: it halts and `z` is a halting value, or it reaches an even
phase or all-ones tape first and `z` is not a halting value, or `z` is a branch value and after `c` phases the
run is at `PE 1 (4 * X x j + 7)`. -/
def Out (p : Ph) (x z : Nat) : Prop :=
  ((∃ g, fate g p = some true) ∧ ∃ k, z = zHalt x k) ∨
  ((∃ g, fate g p = some false) ∧ ¬ ∃ k, z = zHalt x k) ∨
  (∃ j c, z = zB x j ∧ (¬ ∃ k, z = zHalt x k) ∧ ∀ g, fate (g + c) p = fate g (.e 1 (4 * X x j + 7)))

theorem out_step {x z : Nat} (p q : Ph) (hp : next p = some q) (hq : (isEven q || isOnes q) = false)
    (h : Out q x z) : Out p x z := by
  rcases h with ⟨⟨g, hg⟩, hk⟩ | ⟨⟨g, hg⟩, hk⟩ | ⟨j, c, hj, hk, hc⟩
  · exact Or.inl ⟨⟨g + 1, by rw [fate_step p q hp hq]; exact hg⟩, hk⟩
  · exact Or.inr (Or.inl ⟨⟨g + 1, by rw [fate_step p q hp hq]; exact hg⟩, hk⟩)
  · refine Or.inr (Or.inr ⟨j, c + 1, hj, hk, fun g => ?_⟩)
    rw [show g + (c + 1) = (g + c) + 1 by omega, fate_step p q hp hq]; exact hc g

theorem out_false {x z : Nat} (p q : Ph) (hp : next p = some q) (hq : (isEven q || isOnes q) = true)
    (hn : ¬ ∃ k, z = zHalt x k) : Out p x z :=
  Or.inr (Or.inl ⟨⟨1, fate_some 0 p q hp hq⟩, hn⟩)

theorem e_out : ∀ z x, 1 ≤ x → z % 2 = 1 → Out (.e x z) x z := by
  intro z
  induction z using Nat.strongRecOn with
  | _ z ih =>
  intro x hx hz
  have hnot : ∀ k, z = zHalt x k → z = 1 ∨ z ≥ 2 * x + 7 := by
    intro k hk; cases k with
    | zero => left; simpa [zHalt] using hk
    | succ k => right; rw [hk]; exact zHalt_ge (k + 1) x (by omega)
  have hz3 : z = 1 ∨ z = 3 ∨ ∃ w, z = w + 5 := by
    rcases (show z = 1 ∨ z = 3 ∨ z ≥ 5 by omega) with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨z - 5, by omega⟩)
  obtain ⟨m, rfl⟩ : ∃ m, x = m + 1 := ⟨x - 1, by omega⟩
  rcases hz3 with rfl | rfl | ⟨w, rfl⟩
  · exact Or.inl ⟨⟨1, by simp [fate, next]⟩, 0, rfl⟩
  · have hn : ¬ ∃ k, 3 = zHalt (m + 1) k := fun ⟨k, hk⟩ => by rcases hnot k hk with h | h <;> omega
    apply out_step _ (.q (m + 1) 0 1) (by simp [next]) (by simp [isEven, isOnes])
    cases m with
    | zero => exact out_false _ (.e 3 2) (by simp [next]) (by simp [isEven, isOnes]) hn
    | succ m => exact out_false _ (.q m 1 4) (by simp [next]) (by simp [isEven, isOnes]) hn
  · have hnw : ∀ k, w + 5 = zHalt (m + 1) k → w + 5 ≥ 2 * (m + 1) + 7 := fun k hk => by
      rcases hnot k hk with h | h <;> omega
    apply out_step _ (.q (m + 1) 0 (w + 3)) (by simp [next]) (by simp [isEven, isOnes] <;> omega)
    by_cases hb : m + 1 ≤ (w + 2) / 2
    · -- all `m+1` bounces: `Q(0, 2m+2, w+1-2m)`
      have hq : next (.q (m + 1) 0 (w + 3)) = some (.q 0 (2 * (m + 1)) (w + 1 - 2 * m)) := by
        simp only [next, Option.some.injEq, Nat.min_eq_left hb]; congr 1 <;> omega
      apply out_step _ _ hq (by simp [isEven, isOnes] <;> omega)
      have ht3 : w + 1 - 2 * m = 1 ∨ w + 1 - 2 * m = 3 ∨ ∃ t, w + 1 - 2 * m = t + 5 := by
        rcases (show w + 1 - 2 * m = 1 ∨ w + 1 - 2 * m = 3 ∨ w + 1 - 2 * m ≥ 5 by omega) with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨w + 1 - 2 * m - 5, by omega⟩)
      rcases ht3 with h | h | ⟨t, h⟩ <;> rw [h]
      · exact out_false _ (.e 1 (2 * (2 * (m + 1)) + 4)) (by simp [next]) (by simp [isEven, isOnes])
          (fun ⟨k, hk⟩ => by have := hnw k hk; omega)
      · -- the branch: `z = 2x+5`
        refine Or.inr (Or.inr ⟨0, 1, by simp only [zB]; omega, fun ⟨k, hk⟩ => by have := hnw k hk; omega, fun g => ?_⟩)
        rw [fate_step _ (.e 1 (2 * (2 * (m + 1)) + 7)) (by simp [next]) (by simp [isEven, isOnes] <;> omega)]
        simp only [X]; congr 2; omega
      · apply out_step _ (.e (2 * (m + 1) + 4) (t + 1)) (by simp [next]) (by simp [isEven, isOnes] <;> omega)
        have hlt : t + 1 < w + 5 := by omega
        have hshift : ∀ k, w + 5 = zHalt (m + 1) k → ∃ k', t + 1 = zHalt (2 * (m + 1) + 4) k' := by
          intro k hk
          cases k with
          | zero => simp [zHalt] at hk
          | succ k => exact ⟨k, by simp only [zHalt] at hk; omega⟩
        rcases ih (t + 1) hlt (2 * (m + 1) + 4) (by omega) (by omega) with ⟨hf, k, hk⟩ | ⟨hf, hk⟩ | ⟨j, c, hj, hk, hc⟩
        · exact Or.inl ⟨hf, k + 1, by simp only [zHalt]; omega⟩
        · exact Or.inr (Or.inl ⟨hf, fun ⟨k, hk'⟩ => hk (hshift k hk')⟩)
        · refine Or.inr (Or.inr ⟨j + 1, c, by simp only [zB]; omega, fun ⟨k, hk'⟩ => hk (hshift k hk'), ?_⟩)
          simpa only [X] using hc
    · -- the 1s run out first: `Q(m+1-K, 2K, 1)`, then an even phase
      have hq : next (.q (m + 1) 0 (w + 3)) = some (.q (m + 1 - (w + 2) / 2) (2 * ((w + 2) / 2)) 1) := by
        simp only [next, Option.some.injEq, Nat.min_eq_right (by omega : (w + 2) / 2 ≤ m + 1)]; congr 1 <;> omega
      apply out_step _ _ hq (by simp [isEven, isOnes])
      have hn : ¬ ∃ k, w + 5 = zHalt (m + 1) k := fun ⟨k, hk⟩ => by have := hnw k hk; omega
      obtain ⟨r, hr⟩ : ∃ r, m + 1 - (w + 2) / 2 = r + 1 := ⟨m - (w + 2) / 2, by omega⟩
      rw [hr]
      cases r with
      | zero => exact out_false _ (.e 3 (2 * (2 * ((w + 2) / 2)) + 2)) (by simp [next]) (by simp [isEven, isOnes]) hn
      | succ r => exact out_false _ (.q r 1 (2 * (2 * ((w + 2) / 2)) + 4)) (by simp [next]) (by simp [isEven, isOnes]) hn

theorem pow_gt (k : Nat) : k < 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.pow_succ]; omega

/-- The branch target `PE 1 (4 * X 1 j + 7)` is not a halting value of the chain from `PE 1 _`. -/
theorem branch_not_halt (j k : Nat) : 4 * X 1 j + 7 ≠ zHalt 1 k := by
  intro h
  have h1 := X_closed j 1
  have h2 := zHalt_closed k 1
  have hj := pow_gt j
  have hk := pow_gt k
  rw [Nat.pow_succ] at h2
  rcases (show k ≤ j ∨ k = j + 1 ∨ j + 2 ≤ k by omega) with hkj | rfl | hkj
  · have := Nat.pow_le_pow_right (by omega : 2 > 0) hkj
    generalize 2 ^ j = P at *; generalize 2 ^ k = Q at *; omega
  · rw [Nat.pow_succ] at h2 hk
    generalize 2 ^ j = P at *; omega
  · have := Nat.pow_le_pow_right (by omega : 2 > 0) hkj
    rw [Nat.pow_succ, Nat.pow_succ] at this
    generalize 2 ^ j = P at *; generalize 2 ^ k = Q at *; omega

/-- The branch target `PE 1 (4 * X 1 j + 7)` is not a branch value of the chain from `PE 1 _`. -/
theorem branch_not_branch (j k : Nat) : 4 * X 1 j + 7 ≠ zB 1 k := by
  intro h
  have h1 := X_closed j 1
  have h2 := zB_closed k 1
  have hk := pow_gt k
  rw [Nat.pow_succ, Nat.pow_succ] at h2
  rcases (show k ≤ j ∨ j + 1 ≤ k by omega) with hkj | hkj
  · have := Nat.pow_le_pow_right (by omega : 2 > 0) hkj
    generalize 2 ^ j = P at *; generalize 2 ^ k = Q at *; omega
  · have := Nat.pow_le_pow_right (by omega : 2 > 0) hkj
    rw [Nat.pow_succ] at this
    generalize 2 ^ j = P at *; generalize 2 ^ k = Q at *; omega

/-- The all-ones lengths that halt before the next even phase or all-ones tape, for every `n`. -/
def Fatal (n : Nat) : Prop := n = 0 ∨ ∃ k, n + 2 * k + 12 = 20 * 2 ^ k

theorem fatal_iff (n : Nat) : Fatal n ↔ ∃ k, n + 1 = zHalt 1 k := by
  constructor
  · rintro (rfl | ⟨k, hk⟩)
    · exact ⟨0, rfl⟩
    · refine ⟨k + 1, ?_⟩
      have := zHalt_closed (k + 1) 1
      rw [Nat.pow_succ, Nat.pow_succ] at this; generalize 2 ^ k = P at *; omega
  · rintro ⟨k, hk⟩
    cases k with
    | zero => left; simp [zHalt] at hk; omega
    | succ k =>
      right; refine ⟨k, ?_⟩
      have := zHalt_closed (k + 1) 1
      rw [Nat.pow_succ, Nat.pow_succ] at this; generalize 2 ^ k = P at *; omega

theorem ones_fate (n : Nat) :
    ∃ f, (fate f (.r 0 n) = some true ∧ Fatal n) ∨ (fate f (.r 0 n) = some false ∧ ¬ Fatal n) := by
  have hodd : Fatal n → n % 2 = 0 := by
    rintro (h | ⟨k, hk⟩)
    · omega
    · have := pow_gt k
      cases k with
      | zero => simp at hk; omega
      | succ k => rw [Nat.pow_succ] at hk; generalize 2 ^ k = P at hk; omega
  cases n with
  | zero => exact ⟨2, Or.inl ⟨by simp [fate, next, isEven, isOnes], Or.inl rfl⟩⟩
  | succ y =>
    by_cases hy : y % 2 = 0
    · exact ⟨1, Or.inr ⟨fate_some 0 _ (.e 1 (y + 2)) (by simp [next]) (by simp [isEven, isOnes] <;> omega),
        fun h => by have := hodd h; omega⟩⟩
    · have hs := fate_step (.r 0 (y + 1)) (.e 1 (y + 2)) (by simp [next]) (by simp [isEven, isOnes] <;> omega)
      rcases e_out (y + 2) 1 (by omega) (by omega) with ⟨⟨g, hg⟩, hk⟩ | ⟨⟨g, hg⟩, hk⟩ | ⟨j, c, hj, hk, hc⟩
      · exact ⟨g + 1, Or.inl ⟨by rw [hs]; exact hg, (fatal_iff _).mpr hk⟩⟩
      · exact ⟨g + 1, Or.inr ⟨by rw [hs]; exact hg, fun h => hk ((fatal_iff _).mp h)⟩⟩
      · rcases e_out (4 * X 1 j + 7) 1 (by omega) (by omega) with ⟨-, k, hk'⟩ | ⟨⟨g, hg⟩, -⟩ | ⟨j', -, hj', -⟩
        · exact absurd hk' (branch_not_halt j k)
        · exact ⟨g + c + 1, Or.inr ⟨by rw [hs, hc]; exact hg, fun h => hk ((fatal_iff _).mp h)⟩⟩
        · exact absurd hj' (branch_not_branch j j')

/-- **For every `n`**: if `n` is a fatal length, the run from the all-ones tape `PR 0 n` halts. -/
theorem ones_fatal_all (n : Nat) (hf : Fatal n) : TM.Halts trans (PR 0 n) := by
  obtain ⟨f, hfate⟩ := ones_fate n
  rcases hfate with ⟨h, -⟩ | ⟨-, h⟩
  · obtain ⟨k, x, z, hz, hk⟩ := fate_true _ _ h
    obtain ⟨m, -, h1⟩ := reach_iter k _ _ hk
    obtain ⟨m', c', h2, h3⟩ := e_halts x z hz
    exact ⟨m + m', c', steps_seq trans h1 h2, h3⟩
  · exact absurd hf h

/-- **For every `n`**: if `n` is not a fatal length, the run from `PR 0 n` cannot halt before the tape is all ones
again. -/
theorem ones_safe_all (n : Nat) (hf : ¬ Fatal n) :
    ∀ k x z, z ≤ 1 → iter k (.r 0 n) = some (.e x z) → ∃ i, 0 < i ∧ i < k ∧ ∃ m, iter i (.r 0 n) = some (.r 0 m) := by
  intro k x z hz hk
  obtain ⟨f, hfate⟩ := ones_fate n
  rcases hfate with ⟨-, h⟩ | ⟨h, -⟩
  · exact absurd h hf
  obtain ⟨i, q, hi, hq, hc⟩ := fate_false _ _ h
  have hik : i ≤ k := by
    apply Classical.byContradiction; intro hlt
    rw [iter_after_halt k i _ x z hz hk (by omega)] at hq; simp at hq
  have hik' : i < k := by
    rcases Nat.lt_or_eq_of_le hik with h' | rfl
    · exact h'
    · rw [hk] at hq; simp only [Option.some.injEq] at hq; subst hq
      simp [isEven, isOnes] at hc; omega
  obtain ⟨d, rfl⟩ : ∃ d, k = i + d := ⟨k - i, by omega⟩
  rw [iter_add, hq, Option.bind_some] at hk
  rcases hc with he | ho
  · obtain ⟨i', hi'0, hi'd, m, hm⟩ := even_safe d q x z he hz hk
    exact ⟨i + i', by omega, by omega, m, by rw [iter_add, hq, Option.bind_some]; exact hm⟩
  · cases q with
    | r x0 m => simp only [isOnes, beq_iff_eq] at ho; subst ho; exact ⟨i, hi, hik', m, hq⟩
    | e _ _ | q _ _ _ => simp [isOnes] at ho

end H70028
