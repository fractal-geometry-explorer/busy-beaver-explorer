import Phases

/-!
# 1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE: the fatal all-ones lengths, for every n

`Phases.lean` checks by `native_decide`, for `n < 100000`, which all-ones tapes `PR 0 n` halt before the next even
phase or all-ones tape.  Here that is proved for every `n`, by the kernel.  `PR 0 n` goes to `PE 0 (n+1)`.  From
`PE x z` with `z` odd the run is a chain of doublings `PE x z → PE (2x+4) (z-2x-6)`, which halts exactly when
`z = zHalt x k` for some `k` (`e_out`, by strong induction on `z`), and `zHalt 0 k = 8·2^k - 2k - 7`
(`zHalt_closed`).  So `PR 0 n` is fatal iff `n = 0`, `n = 6` or `n = 32·2^k - 2k - 12` (`Fatal`, `ones_fate`,
`ones_fatal_all`, `ones_safe_all`).
-/

namespace H137865

open TM

/-- The `z` values from which `PE x z` halts before an even phase or an all-ones tape. -/
def zHalt : Nat → Nat → Nat
  | _, 0 => 1
  | x, k + 1 => zHalt (2 * x + 4) k + 2 * x + 6

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
phase or all-ones tape first and `z` is not a halting value. -/
def Out (p : Ph) (x z : Nat) : Prop :=
  ((∃ g, fate g p = some true) ∧ ∃ k, z = zHalt x k) ∨
  ((∃ g, fate g p = some false) ∧ ¬ ∃ k, z = zHalt x k)

theorem out_step {x z : Nat} (p q : Ph) (hp : next p = some q) (hq : (isEven q || isOnes q) = false)
    (h : Out q x z) : Out p x z := by
  rcases h with ⟨⟨g, hg⟩, hk⟩ | ⟨⟨g, hg⟩, hk⟩
  · exact Or.inl ⟨⟨g + 1, by rw [fate_step p q hp hq]; exact hg⟩, hk⟩
  · exact Or.inr ⟨⟨g + 1, by rw [fate_step p q hp hq]; exact hg⟩, hk⟩

theorem out_false {x z : Nat} (p q : Ph) (hp : next p = some q) (hq : (isEven q || isOnes q) = true)
    (hn : ¬ ∃ k, z = zHalt x k) : Out p x z :=
  Or.inr ⟨⟨1, fate_some 0 p q hp hq⟩, hn⟩

/-- One doubling, as a step of the induction: `Out` for `PE (2x+4) z'` gives `Out` for `PE x (z'+2x+6)`. -/
theorem out_shift {x z z' : Nat} (p : Ph) (hz : z = z' + 2 * x + 6) (h : Out p (2 * x + 4) z') : Out p x z := by
  have hshift : ∀ k, z = zHalt x k → ∃ k', z' = zHalt (2 * x + 4) k' := by
    intro k hk
    cases k with
    | zero => simp [zHalt] at hk; omega
    | succ k => exact ⟨k, by simp only [zHalt] at hk; omega⟩
  rcases h with ⟨hf, k, hk⟩ | ⟨hf, hk⟩
  · exact Or.inl ⟨hf, k + 1, by simp only [zHalt]; omega⟩
  · exact Or.inr ⟨hf, fun ⟨k, hk'⟩ => hk (hshift k hk')⟩

theorem e_out : ∀ z x, z % 2 = 1 → Out (.e x z) x z := by
  intro z
  induction z using Nat.strongRecOn with
  | _ z ih =>
  intro x hz
  have hnot : ∀ k, z = zHalt x k → z = 1 ∨ z ≥ 2 * x + 7 := by
    intro k hk; cases k with
    | zero => left; simpa [zHalt] using hk
    | succ k => right; rw [hk]; exact zHalt_ge (k + 1) x (by omega)
  have hz3 : z = 1 ∨ z = 3 ∨ ∃ w, z = w + 5 := by
    rcases (show z = 1 ∨ z = 3 ∨ z ≥ 5 by omega) with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨z - 5, by omega⟩)
  rcases hz3 with rfl | rfl | ⟨w, rfl⟩
  · exact Or.inl ⟨⟨1, by simp [fate, next]⟩, 0, rfl⟩
  · have hn : ¬ ∃ k, 3 = zHalt x k := fun ⟨k, hk⟩ => by rcases hnot k hk with h | h <;> omega
    cases x with
    | zero =>
      apply out_step _ (.q 0 0 1) (by simp [next]) (by simp [isEven, isOnes])
      exact out_false _ (.r 0 5) (by simp [next]) (by simp [isEven, isOnes]) hn
    | succ m =>
      apply out_step _ (.q (m + 1) 0 1) (by simp [next]) (by simp [isEven, isOnes])
      exact out_false _ (.r (m + 1) 5) (by simp [next]) (by simp [isEven, isOnes]) hn
  · have hnw : ∀ k, w + 5 = zHalt x k → w + 5 ≥ 2 * x + 7 := fun k hk => by
      rcases hnot k hk with h | h <;> omega
    cases x with
    | zero =>
      apply out_step _ (.q 0 0 (w + 3)) (by simp [next]) (by simp [isEven, isOnes] <;> omega)
      obtain ⟨t, rfl⟩ | rfl : (∃ t, w = t + 2) ∨ w = 0 := by
        rcases Nat.lt_or_ge w 2 with h | h
        · right; omega
        · left; exact ⟨w - 2, by omega⟩
      · apply out_step _ (.e 4 (t + 1)) (by simp [next]) (by simp [isEven, isOnes] <;> omega)
        exact out_shift _ (by omega) (ih (t + 1) (by omega) 4 (by omega))
      · exact out_false _ (.r 0 8) (by simp [next]) (by simp [isEven, isOnes])
          (fun ⟨k, hk⟩ => by have := hnw k hk; omega)
    | succ m =>
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
      · exact out_false _ (.r 0 (2 * (2 * (m + 1)) + 5)) (by simp [next]) (by simp [isEven, isOnes])
          (fun ⟨k, hk⟩ => by have := hnw k hk; omega)
      · exact out_false _ (.r 0 (2 * (2 * (m + 1)) + 8)) (by simp [next]) (by simp [isEven, isOnes])
          (fun ⟨k, hk⟩ => by have := hnw k hk; omega)
      · apply out_step _ (.e (2 * (m + 1) + 4) (t + 1)) (by simp [next]) (by simp [isEven, isOnes] <;> omega)
        exact out_shift _ (by omega) (ih (t + 1) (by omega) (2 * (m + 1) + 4) (by omega))
    · -- the 1s run out first: `Q(m+1-K, 2K, 1)`, then an even phase
      have hq : next (.q (m + 1) 0 (w + 3)) = some (.q (m + 1 - (w + 2) / 2) (2 * ((w + 2) / 2)) 1) := by
        simp only [next, Option.some.injEq, Nat.min_eq_right (by omega : (w + 2) / 2 ≤ m + 1)]; congr 1 <;> omega
      apply out_step _ _ hq (by simp [isEven, isOnes])
      exact out_false _ (.r (m + 1 - (w + 2) / 2) (2 * (2 * ((w + 2) / 2)) + 5)) (by simp [next])
        (by simp [isEven, isOnes] <;> omega) (fun ⟨k, hk⟩ => by have := hnw k hk; omega)

theorem pow_gt (k : Nat) : k < 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.pow_succ]; omega

/-- The all-ones lengths that halt before the next even phase or all-ones tape, for every `n`. -/
def Fatal (n : Nat) : Prop := n = 0 ∨ n = 6 ∨ ∃ k, n + 2 * k + 12 = 32 * 2 ^ k

theorem fatal_iff (n : Nat) : Fatal n ↔ ∃ k, n + 1 = zHalt 0 k := by
  constructor
  · rintro (rfl | rfl | ⟨k, hk⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · refine ⟨k + 2, ?_⟩
      have := zHalt_closed (k + 2) 0
      rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ] at this; generalize 2 ^ k = P at *; omega
  · rintro ⟨k, hk⟩
    match k, hk with
    | 0, hk => left; simp [zHalt] at hk; omega
    | 1, hk => right; left; simp [zHalt] at hk; omega
    | k + 2, hk =>
      right; right; refine ⟨k, ?_⟩
      have := zHalt_closed (k + 2) 0
      rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ] at this; generalize 2 ^ k = P at *; omega

theorem ones_fate (n : Nat) :
    ∃ f, (fate f (.r 0 n) = some true ∧ Fatal n) ∨ (fate f (.r 0 n) = some false ∧ ¬ Fatal n) := by
  have hodd : Fatal n → n % 2 = 0 := by
    rintro (h | h | ⟨k, hk⟩)
    · omega
    · omega
    · have := pow_gt k
      cases k with
      | zero => simp at hk; omega
      | succ k => rw [Nat.pow_succ] at hk; generalize 2 ^ k = P at hk; omega
  cases n with
  | zero => exact ⟨2, Or.inl ⟨by simp [fate, next, isEven, isOnes], Or.inl rfl⟩⟩
  | succ y =>
    by_cases hy : y % 2 = 0
    · exact ⟨1, Or.inr ⟨fate_some 0 _ (.e 0 (y + 2)) (by simp [next]) (by simp [isEven, isOnes] <;> omega),
        fun h => by have := hodd h; omega⟩⟩
    · have hs := fate_step (.r 0 (y + 1)) (.e 0 (y + 2)) (by simp [next]) (by simp [isEven, isOnes] <;> omega)
      rcases e_out (y + 2) 0 (by omega) with ⟨⟨g, hg⟩, hk⟩ | ⟨⟨g, hg⟩, hk⟩
      · exact ⟨g + 1, Or.inl ⟨by rw [hs]; exact hg, (fatal_iff _).mpr hk⟩⟩
      · exact ⟨g + 1, Or.inr ⟨by rw [hs]; exact hg, fun h => hk ((fatal_iff _).mp h)⟩⟩

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

end H137865
