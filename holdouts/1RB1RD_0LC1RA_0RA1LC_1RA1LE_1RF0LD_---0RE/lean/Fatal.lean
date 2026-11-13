import Phases

/-!
# 1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE: the fatal all-ones lengths, for every n

`Phases.lean` checks by `native_decide`, for `n < 100000`, which all-ones tapes `PA 0 n` halt before the next even
phase or all-ones tape.  Here that is proved for every `n`, by the kernel: from `PE x z` with `z` odd the run is a
chain of doublings `PE x z → PE (2x+4) (z-2x-6)`, which halts exactly when `z = zHalt x k` for some `k`
(`e_fate`, by strong induction on `z`), and `zHalt 2 k = 12·2^k - 2k - 11` (`zHalt_closed`).  So `PA 0 n` is fatal
iff `n = 1` or `n = 12·2^k - 2k - 9` (`Fatal`, `ones_fate`, `ones_fatal_all`, `ones_safe_all`).
-/

namespace H113619

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

theorem fate_cont (f : Nat) (p q : Ph) (hp : next p = some q) (hq : (isEven q || isOnes q) = false) :
    fate (f + 1) p = fate f q := by simp [fate, hp, hq]

/-- From `PE x z` with `z` odd and `x ≥ 1`, the run halts before an even phase or all-ones tape exactly when
`z = zHalt x k` for some `k`. -/
theorem e_fate : ∀ z x f, 1 ≤ x → z % 2 = 1 → z ≤ f →
    (fate (f + 1) (.e x z) = some true ∧ ∃ k, z = zHalt x k) ∨
    (fate (f + 1) (.e x z) = some false ∧ ¬ ∃ k, z = zHalt x k) := by
  intro z
  induction z using Nat.strongRecOn with
  | _ z ih =>
  intro x f hx hz hf
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
  · left; exact ⟨by simp [fate, next], 0, rfl⟩
  · right
    obtain ⟨m, rfl⟩ : ∃ m, x = m + 1 := ⟨x - 1, by omega⟩
    refine ⟨?_, fun ⟨k, hk⟩ => by rcases hnot k hk with h | h <;> omega⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [fate_cont _ _ (.q (m + 1) 0 1) (by simp [next]) (by simp [isEven, isOnes])]
    exact fate_some _ _ (.a (m + 1) 4) (by simp [next]) (by simp [isEven, isOnes])
  · obtain ⟨m, rfl⟩ : ∃ m, x = m + 1 := ⟨x - 1, by omega⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 3 := ⟨f - 3, by omega⟩
    rw [fate_cont _ _ (.q (m + 1) 0 (w + 3)) (by simp [next]) (by simp [isEven, isOnes]; omega)]
    by_cases hb : m + 1 ≤ (w + 2) / 2
    · -- all `m+1` bounces: `Q(0, m+1, w+1-2m)`
      have hq : next (.q (m + 1) 0 (w + 3)) = some (.q 0 (m + 1) (w + 1 - 2 * m)) := by
        simp only [next, Option.some.injEq, Nat.min_eq_left hb]; congr 1 <;> omega
      rw [fate_cont _ _ _ hq (by simp [isEven, isOnes]; omega)]
      have ht3 : w + 1 - 2 * m = 1 ∨ w + 1 - 2 * m = 3 ∨ ∃ t, w + 1 - 2 * m = t + 5 := by
        rcases (show w + 1 - 2 * m = 1 ∨ w + 1 - 2 * m = 3 ∨ w + 1 - 2 * m ≥ 5 by omega) with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨w + 1 - 2 * m - 5, by omega⟩)
      rcases ht3 with h | h | ⟨t, h⟩
      · right; rw [h]
        refine ⟨fate_some _ _ (.a 0 (4 * (m + 1) + 4)) (by simp [next]) (by simp [isEven, isOnes]), ?_⟩
        rintro ⟨k, hk⟩; rcases hnot k hk with h' | h' <;> omega
      · right; rw [h]
        refine ⟨fate_some _ _ (.a 0 (4 * (m + 1) + 7)) (by simp [next]) (by simp [isEven, isOnes]), ?_⟩
        rintro ⟨k, hk⟩; rcases hnot k hk with h' | h' <;> omega
      · rw [h]
        obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
        rw [fate_cont _ _ (.e (2 * (m + 1) + 4) (t + 1)) (by simp [next]) (by simp [isEven, isOnes]; omega)]
        have hlt : t + 1 < w + 5 := by omega
        rcases ih (t + 1) hlt (2 * (m + 1) + 4) (g' + 1) (by omega) (by omega) (by omega) with ⟨h1, k, hk⟩ | ⟨h1, hk⟩
        · left; exact ⟨h1, k + 1, by simp only [zHalt]; omega⟩
        · right; refine ⟨h1, ?_⟩
          rintro ⟨k, hk'⟩
          cases k with
          | zero => simp [zHalt] at hk'
          | succ k => exact hk ⟨k, by simp only [zHalt] at hk'; omega⟩
    · -- the 1s run out first: `Q(m+1-K, K, 1)`, then an even `PA`
      right
      have hq : next (.q (m + 1) 0 (w + 3)) = some (.q (m + 1 - (w + 2) / 2) ((w + 2) / 2) 1) := by
        simp only [next, Option.some.injEq, Nat.min_eq_right (by omega : (w + 2) / 2 ≤ m + 1)]; congr 1 <;> omega
      rw [fate_cont _ _ _ hq (by simp [isEven, isOnes])]
      refine ⟨fate_some _ _ (.a (m + 1 - (w + 2) / 2) (4 * ((w + 2) / 2) + 4)) (by simp [next])
        (by simp [isEven, isOnes]; omega), ?_⟩
      rintro ⟨k, hk⟩; rcases hnot k hk with h' | h' <;> omega

theorem pow_gt (k : Nat) : k < 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.pow_succ]; omega

/-- The all-ones lengths that halt before the next even phase or all-ones tape, for every `n`. -/
def Fatal (n : Nat) : Prop := n = 1 ∨ ∃ k, n + 2 * k + 9 = 12 * 2 ^ k

theorem ones_fate : ∀ n, (fate (n + 4) (.a 0 n) = some true ∧ Fatal n) ∨ (fate (n + 4) (.a 0 n) = some false ∧ ¬ Fatal n) := by
  intro n
  have hodd : ∀ k, (n + 2 * k + 9 = 12 * 2 ^ k) → n % 2 = 1 := by
    intro k hk; generalize 2 ^ k = P at hk; omega
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n ≥ 3 by omega) with rfl | rfl | rfl | h3
  · right; refine ⟨fate_some _ _ (.a 0 2) (by simp [next]) (by simp [isEven, isOnes]), ?_⟩
    rintro (h | ⟨k, hk⟩)
    · omega
    · have := hodd k hk; omega
  · left; exact ⟨by simp [fate, next, isEven, isOnes], Or.inl rfl⟩
  · right; refine ⟨fate_some _ _ (.a 0 5) (by simp [next]) (by simp [isEven, isOnes]), ?_⟩
    rintro (h | ⟨k, hk⟩)
    · omega
    · have := hodd k hk; omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    by_cases hm : m % 2 = 1
    · right
      refine ⟨fate_some _ _ (.e 2 (m + 1)) (by simp [next]) (by simp [isEven, isOnes]; omega), ?_⟩
      rintro (h | ⟨k, hk⟩)
      · omega
      · have := hodd k hk; omega
    · rw [show m + 3 + 4 = (m + 5) + 1 + 1 by omega,
        fate_cont _ _ (.e 2 (m + 1)) (by simp [next]) (by simp [isEven, isOnes]; omega)]
      have hiff : (∃ k, m + 1 = zHalt 2 k) ↔ Fatal (m + 3) := by
        constructor
        · rintro ⟨k, hk⟩; right; refine ⟨k, ?_⟩
          have := zHalt_closed k 2
          rw [Nat.pow_succ] at this; generalize 2 ^ k = P at *; omega
        · rintro (h | ⟨k, hk⟩)
          · omega
          · refine ⟨k, ?_⟩
            have := zHalt_closed k 2
            rw [Nat.pow_succ] at this; generalize 2 ^ k = P at *; omega
      rcases e_fate (m + 1) 2 (m + 5) (by omega) (by omega) (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨h1, hiff.mp h2⟩
      · right; exact ⟨h1, fun h => h2 (hiff.mpr h)⟩

/-- **For every `n`**: if `n` is a fatal length, the run from the all-ones tape `PA 0 n` halts. -/
theorem ones_fatal_all (n : Nat) (hf : Fatal n) : TM.Halts trans (PA 0 n) := by
  rcases ones_fate n with ⟨h, -⟩ | ⟨-, h⟩
  · obtain ⟨k, x, z, hz, hk⟩ := fate_true _ _ h
    obtain ⟨m, -, h1⟩ := reach_iter k _ _ hk
    obtain ⟨m', c', h2, h3⟩ := e_halts x z hz
    exact ⟨m + m', c', steps_seq trans h1 h2, h3⟩
  · exact absurd hf h

/-- **For every `n`**: if `n` is not a fatal length, the run from `PA 0 n` cannot halt before the tape is all ones
again. -/
theorem ones_safe_all (n : Nat) (hf : ¬ Fatal n) :
    ∀ k x z, z ≤ 1 → iter k (.a 0 n) = some (.e x z) → ∃ i, 0 < i ∧ i < k ∧ ∃ m, iter i (.a 0 n) = some (.a 0 m) := by
  intro k x z hz hk
  rcases ones_fate n with ⟨-, h⟩ | ⟨h, -⟩
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
    | a x0 m => simp only [isOnes, beq_iff_eq] at ho; subst ho; exact ⟨i, hi, hik', m, hq⟩
    | e _ _ | q _ _ _ => simp [isOnes] at ho

end H113619
