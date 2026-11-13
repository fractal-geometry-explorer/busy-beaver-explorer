import Macro

/-!
# Space Needle: Doucette's one-variable map

Write `D = 2^v · E` with `E` odd (`v = v2 D`, `E = odd D`) and let `F D = D + v + 3 · (E / 2)`
(Katelyn Doucette's form, `b + v(b) + (3/2)(odd − 1)`).  The configurations `(b, 1)` of the orbit of `g` are
`b = Fit k − 3` with `Fit 0 = 6`, `Fit (k+1) = F (Fit k)`, and between two of them the orbit takes `v2 D` odd steps
(halving `D`) and one even step.  The machine halts exactly when some `Fit k` is a power of two
(`halts_iff_pow2`): then the odd steps run down to `b = 1`.
-/

namespace H101957

/-- `v2f fuel n`: the number of factors 2 of `n` (for `n ≤ fuel`). -/
def v2f : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => if n ≠ 0 ∧ n % 2 = 0 then v2f f (n / 2) + 1 else 0

/-- The 2-adic valuation. -/
def v2 (n : Nat) : Nat := v2f n n

/-- The odd part. -/
def odd (n : Nat) : Nat := n / 2 ^ v2 n

theorem v2f_spec : ∀ (f n : Nat), n ≠ 0 → n ≤ f →
    2 ^ v2f f n * (n / 2 ^ v2f f n) = n ∧ (n / 2 ^ v2f f n) % 2 = 1 := by
  intro f
  induction f with
  | zero => intro n h0 hf; omega
  | succ f ih =>
    intro n h0 hf
    by_cases h : n % 2 = 0
    · have hv : v2f (f + 1) n = v2f f (n / 2) + 1 := by simp [v2f, h0, h]
      have h2 : n / 2 ≠ 0 := by omega
      obtain ⟨ih1, ih2⟩ := ih (n / 2) h2 (by omega)
      rw [hv]
      have e : n / 2 ^ (v2f f (n / 2) + 1) = n / 2 / 2 ^ v2f f (n / 2) := by
        rw [Nat.pow_succ, Nat.mul_comm, Nat.div_div_eq_div_mul]
      rw [e]
      refine ⟨?_, ih2⟩
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ _) 2, Nat.mul_assoc, ih1]
      omega
    · have hv : v2f (f + 1) n = 0 := by simp [v2f, h]
      rw [hv]; simp; omega

theorem odd_spec (n : Nat) (h : n ≠ 0) : 2 ^ v2 n * odd n = n ∧ odd n % 2 = 1 :=
  v2f_spec n n h (Nat.le_refl n)

/-- Doucette's map. -/
def F (D : Nat) : Nat := D + v2 D + 3 * (odd D / 2)

/-- Its orbit from 6. -/
def Fit : Nat → Nat
  | 0 => 6
  | k + 1 => F (Fit k)

theorem F_ge (D : Nat) : D ≤ F D := by unfold F; omega

theorem Fit_ge (k : Nat) : 6 ≤ Fit k := by
  induction k with
  | zero => simp [Fit]
  | succ k ih => exact Nat.le_trans ih (F_ge _)

/-! ## Iterating `g` -/

def giter : Nat → Nat × Nat → Nat × Nat
  | 0, p => p
  | n + 1, p => giter n (g p)

theorem giter_succ' (n : Nat) (p : Nat × Nat) : giter (n + 1) p = g (giter n p) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => exact ih (g p)

theorem orbit_add (n m : Nat) : orbit (n + m) = giter m (orbit n) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [← Nat.add_assoc, orbit_succ, ih, giter_succ']

/-- `j` odd steps: `(2^j E − 3, c)` goes to `(E − 3, c + j + 2^j E − E)`, through values of b other than 1. -/
theorem oddchain (j : Nat) : ∀ (E c : Nat), 3 ≤ E →
    giter j (2 ^ j * E - 3, c) = (E - 3, c + j + (2 ^ j * E - E)) ∧
    ∀ i < j, (giter i (2 ^ j * E - 3, c)).1 ≠ 1 := by
  induction j with
  | zero => intro E c _; simp [giter]
  | succ j ih =>
    intro E c hE
    have hx : E ≤ 2 ^ j * E := Nat.le_mul_of_pos_left E (Nat.pow_pos (by omega))
    have e2 : 2 ^ (j + 1) * E = 2 * (2 ^ j * E) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_assoc]
    obtain ⟨x, hxd⟩ : ∃ x, x = 2 ^ j * E := ⟨_, rfl⟩
    rw [e2, ← hxd]
    rw [← hxd] at hx
    have hg : g (2 * x - 3, c) = (x - 3, x + c + 1) := by
      have := g_odd (x - 3) c
      rw [show 2 * (x - 3) + 1 + 2 = 2 * x - 3 by omega, show x - 3 + c + 4 = x + c + 1 by omega] at this
      exact this
    obtain ⟨h1, h2⟩ := ih E (x + c + 1) hE
    rw [← hxd] at h1 h2
    refine ⟨?_, ?_⟩
    · show giter j (g (2 * x - 3, c)) = _
      rw [hg, h1]
      congr 1
      omega
    · intro i hi
      cases i with
      | zero => show 2 * x - 3 ≠ 1; omega
      | succ i =>
        show (giter i (g (2 * x - 3, c))).1 ≠ 1
        rw [hg]
        exact h2 i (by omega)

/-- From `(D − 3, 1)` with `D` not a power of two, `v2 D + 1` steps of `g` lead to `(F D − 3, 1)`, never through
b = 1. -/
theorem macro_F (D : Nat) (hD : 6 ≤ D) (hE : odd D ≠ 1) :
    giter (v2 D + 1) (D - 3, 1) = (F D - 3, 1) ∧ ∀ i < v2 D + 1, (giter i (D - 3, 1)).1 ≠ 1 := by
  obtain ⟨hs, ho⟩ := odd_spec D (by omega)
  obtain ⟨a, ha⟩ : ∃ a, odd D = 2 * a + 1 := ⟨odd D / 2, by omega⟩
  have ha1 : 1 ≤ a := by omega
  have hdiv : odd D / 2 = a := by omega
  have hc := oddchain (v2 D) (odd D) 1 (by omega)
  rw [hs] at hc
  obtain ⟨h1, h2⟩ := hc
  have hEle : odd D ≤ D := by
    have := Nat.le_mul_of_pos_left (odd D) (Nat.pow_pos (n := v2 D) (by omega : 0 < 2))
    omega
  have hlast : g (odd D - 3, 1 + v2 D + (D - odd D)) = (F D - 3, 1) := by
    unfold F
    rw [hdiv, ha]
    by_cases h : a = 1
    · subst h
      rw [show 2 * 1 + 1 - 3 = 0 by omega, g_zero]
      congr 1
      omega
    · have := g_even (a - 2) (1 + v2 D + (D - (2 * a + 1)))
      rw [show 2 * (a - 2) + 2 = 2 * a + 1 - 3 by omega] at this
      rw [this]
      congr 1
      omega
  refine ⟨?_, ?_⟩
  · rw [giter_succ', h1, hlast]
  · intro i hi
    by_cases h : i < v2 D
    · exact h2 i h
    · rw [show i = v2 D by omega, h1]
      show odd D - 3 ≠ 1
      omega

/-- From `(D − 3, 1)` with `D ≥ 6` a power of two, the odd steps reach b = 1. -/
theorem macro_pow2 (D : Nat) (hD : 6 ≤ D) (hE : odd D = 1) : ∃ i, (giter i (D - 3, 1)).1 = 1 := by
  obtain ⟨hs, _⟩ := odd_spec D (by omega)
  rw [hE, Nat.mul_one] at hs
  -- D = 2^v with v ≥ 3, so D = 2^(v-2) · 4
  have hv : 3 ≤ v2 D := by
    rcases Nat.lt_or_ge (v2 D) 3 with h | h
    · have : 2 ^ v2 D ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    · exact h
  have e : D = 2 ^ (v2 D - 2) * 4 := by
    rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add, Nat.sub_add_cancel (by omega)]
    exact hs.symm
  obtain ⟨h1, _⟩ := oddchain (v2 D - 2) 4 1 (by omega)
  refine ⟨v2 D - 2, ?_⟩
  rw [← e] at h1
  rw [h1]

theorem orbit_Fit (k : Nat) :
    (∃ k' < k, odd (Fit k') = 1) ∨ (∃ N, k ≤ N ∧ orbit N = (Fit k - 3, 1) ∧ ∀ i < N, (orbit i).1 ≠ 1) := by
  induction k with
  | zero => exact Or.inr ⟨0, Nat.le_refl 0, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ k ih =>
    rcases ih with ⟨k', hk', hp⟩ | ⟨N, hN, ho, hb⟩
    · exact Or.inl ⟨k', by omega, hp⟩
    · by_cases hp : odd (Fit k) = 1
      · exact Or.inl ⟨k, Nat.lt_succ_self k, hp⟩
      · obtain ⟨m1, m2⟩ := macro_F (Fit k) (Fit_ge k) hp
        refine Or.inr ⟨N + (v2 (Fit k) + 1), by omega, ?_, ?_⟩
        · rw [orbit_add, ho, m1]; rfl
        · intro i hi
          by_cases h : i < N
          · exact hb i h
          · obtain ⟨d, rfl⟩ : ∃ d, i = N + d := ⟨i - N, by omega⟩
            rw [orbit_add, ho]
            exact m2 d (by omega)

/-- **Doucette's form.** The orbit of `g` reaches b = 1 exactly when some `Fit k` is a power of two
(odd part 1). -/
theorem orbit_iff_pow2 : (∃ n, (orbit n).1 = 1) ↔ ∃ k, odd (Fit k) = 1 := by
  constructor
  · rintro ⟨n, hn⟩
    rcases orbit_Fit (n + 1) with ⟨k', _, hp⟩ | ⟨N, hN, _, hb⟩
    · exact ⟨k', hp⟩
    · exact absurd hn (hb n (by omega))
  · rintro ⟨k, hk⟩
    obtain ⟨k0, hk0, hmin⟩ := exists_min (fun k => odd (Fit k) = 1) k hk
    rcases orbit_Fit k0 with ⟨k', hk', hp⟩ | ⟨N, _, ho, _⟩
    · exact absurd hp (hmin k' hk')
    · obtain ⟨i, hi⟩ := macro_pow2 (Fit k0) (Fit_ge k0) hk0
      exact ⟨N + i, by rw [orbit_add, ho]; exact hi⟩

/-- **Space Needle halts from blank tape if and only if Doucette's sequence 6, 10, 17, 41, 101, ... reaches a power
of two.** -/
theorem halts_iff_pow2 : HaltsFromBlank ↔ ∃ k, odd (Fit k) = 1 :=
  halts_iff.trans orbit_iff_pow2

end H101957
