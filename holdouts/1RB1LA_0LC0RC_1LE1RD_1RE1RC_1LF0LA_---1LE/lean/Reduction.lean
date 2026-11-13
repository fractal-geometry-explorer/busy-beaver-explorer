import Macro

/-!
# 1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE: the halting problem of the machine is a question about one orbit

`F (p, q)` is the sample map of `Macro.lean` (with `F (1, q) = (1, q)`: p = 1 is where the machine halts), and
`orbit n = F^n (0, 2)`.  Proved here:

* `reach`: blank tape reaches `K (orbit n)` after exactly `time n` steps, for every n;
* `halts_iff`: **the machine halts from blank tape iff some `orbit n` has p = 1**;
* `halts_iff_pow2`: **it halts iff some sample with q = 1 has p + 3 a power of two**;
* `time_lt_of_halts`: if it halts, it runs more than `time n` steps, for every n.
-/

namespace H31371

open TM

/-- The sample map: K(p, q) ↦ K(F (p, q)). -/
def F (x : Nat × Nat) : Nat × Nat :=
  if x.1 = 0 then (2, x.2 - 1)
  else if x.1 = 1 then x
  else if x.1 % 2 = 1 then ((x.1 - 3) / 2, x.2 + (x.1 + 5) / 2)
  else (3 * x.1 / 2 + x.2, 1)

/-- The number of machine steps from K(x) to K(F x) (0 at p = 1). -/
def T (x : Nat × Nat) : Nat :=
  if x.1 = 0 then 7
  else if x.1 = 1 then 0
  else if x.1 % 2 = 1 then 2 * ((x.1 - 3) / 2) * ((x.1 - 3) / 2) + 10 * ((x.1 - 3) / 2) + 13
  else x.2 * (4 * ((x.1 - 2) / 2) + 8) + 6 * ((x.1 - 2) / 2) * ((x.1 - 2) / 2) + 22 * ((x.1 - 2) / 2) + 15

/-- The samples of the run from blank tape: `orbit n = F^n (0, 2)`. -/
def orbit : Nat → Nat × Nat
  | 0 => (0, 2)
  | n + 1 => F (orbit n)

/-- The step at which the run from blank tape is at `K (orbit n)`. -/
def time : Nat → Nat
  | 0 => 7
  | n + 1 => time n + T (orbit n)

/-- p = 0 comes with q ≥ 1 (true on the orbit; K 0 0 does not occur). -/
def Inv (x : Nat × Nat) : Prop := x.1 = 0 → 1 ≤ x.2

theorem F_inv (x : Nat × Nat) : Inv (F x) := by
  unfold Inv F
  by_cases h0 : x.1 = 0
  · simp [h0]
  · by_cases h1 : x.1 = 1
    · simp [h1]
    · by_cases h2 : x.1 % 2 = 1
      · simp only [h0, h1, h2, ite_false, ite_true]; intro; omega
      · simp only [h0, h1, h2, ite_false]; intro; omega

theorem K_step (x : Nat × Nat) (h : Inv x) : steps (T x) (K x.1 x.2) = some (K (F x).1 (F x).2) := by
  obtain ⟨p, q⟩ := x
  unfold Inv at h
  simp only at h
  by_cases h0 : p = 0
  · subst h0
    obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    simpa [F, T] using K_zero q
  · by_cases h1 : p = 1
    · subst h1; simp [F, T]
    · by_cases h2 : p % 2 = 1
      · obtain ⟨k, rfl⟩ : ∃ k, p = 2 * k + 3 := ⟨(p - 3) / 2, by omega⟩
        have eF : F (2 * k + 3, q) = (k, q + k + 4) := by
          simp only [F, h0, h1, h2, ite_false, ite_true]; ext <;> simp <;> omega
        have eT : T (2 * k + 3, q) = 2 * k * k + 10 * k + 13 := by
          simp only [T, h0, h1, h2, ite_false, ite_true]
          rw [show (2 * k + 3 - 3) / 2 = k by omega]
        rw [eF, eT]; exact K_odd k q
      · obtain ⟨k, rfl⟩ : ∃ k, p = 2 * k + 2 := ⟨(p - 2) / 2, by omega⟩
        have eF : F (2 * k + 2, q) = (3 * k + 3 + q, 1) := by
          simp only [F, h0, h1, h2, ite_false]; ext <;> simp <;> omega
        have eT : T (2 * k + 2, q) = q * (4 * k + 8) + 6 * k * k + 22 * k + 15 := by
          simp only [T, h0, h1, h2, ite_false]
          rw [show (2 * k + 2 - 2) / 2 = k by omega]
        rw [eF, eT]; exact K_even k q

theorem orbit_inv (n : Nat) : Inv (orbit n) := by
  cases n with
  | zero => intro h; simp [orbit]
  | succ n => exact F_inv _

/-- Blank tape reaches `K (orbit n)` after exactly `time n` steps. -/
theorem reach (n : Nat) : steps (time n) init = some (K (orbit n).1 (orbit n).2) := by
  induction n with
  | zero => exact blank_K
  | succ n ih => exact steps_seq trans ih (K_step _ (orbit_inv n))

theorem T_pos (x : Nat × Nat) (h : x.1 ≠ 1) : 1 ≤ T x := by
  unfold T
  by_cases h0 : x.1 = 0
  · simp [h0]
  · by_cases h2 : x.1 % 2 = 1
    · simp only [h0, h, h2, ite_false, ite_true]; omega
    · simp only [h0, h, h2, ite_false]; omega

theorem halts_of_steps {c c' : Config} {t : Nat} (h : steps t c = some c') (hc : TM.Halts trans c') :
    TM.Halts trans c := by
  obtain ⟨n, c'', h1, h2⟩ := hc
  exact ⟨t + n, c'', steps_seq trans h h1, h2⟩

/-- **The reduction**: the machine halts from blank tape iff the orbit of (0, 2) under `F` reaches p = 1. -/
theorem halts_iff : HaltsFromBlank ↔ ∃ n, (orbit n).1 = 1 := by
  constructor
  · intro hh
    refine Classical.byContradiction fun hn => ?_
    have hne : ∀ n, (orbit n).1 ≠ 1 := fun n e => hn ⟨n, e⟩
    have ht : ∀ n, n ≤ time n := by
      intro n
      induction n with
      | zero => simp [time]
      | succ n ih => have := T_pos _ (hne n); simp only [time]; omega
    apply not_halts_of_forall trans _ hh
    apply forall_of_unbounded trans (fun m => ∃ n, time n = m)
    · intro n; exact ⟨time n, ht n, n, rfl⟩
    · rintro m ⟨n, rfl⟩; exact ⟨_, reach n⟩
  · rintro ⟨n, hn⟩
    have h := reach n
    rw [hn] at h
    exact halts_of_steps h (K_one_halts _)

/-- Before p reaches 1, an odd p comes from a sample K(p₀, 1) with p₀ + 3 = 2^b · (p + 3). -/
theorem odd_from_q1 (n : Nat) (h : (orbit n).1 % 2 = 1) :
    ∃ m b, (orbit m).2 = 1 ∧ (orbit m).1 + 3 = 2 ^ b * ((orbit n).1 + 3) := by
  induction n with
  | zero => simp [orbit] at h
  | succ n ih =>
    simp only [orbit] at h ⊢
    generalize hx : orbit n = x at h ih
    unfold F at h ⊢
    by_cases h0 : x.1 = 0
    · simp [h0] at h
    · by_cases h1 : x.1 = 1
      · simp only [h1, ↓reduceIte] at h ⊢
        obtain ⟨m, b, hm, hb⟩ := ih h
        exact ⟨m, b, hm, hb⟩
      · by_cases h2 : x.1 % 2 = 1
        · simp only [h0, h1, h2, ite_true, ite_false] at h ⊢
          obtain ⟨m, b, hm, hb⟩ := ih h2
          refine ⟨m, b + 1, hm, ?_⟩
          rw [hb, Nat.pow_succ, Nat.mul_assoc]
          congr 1; omega
        · simp only [h0, h1, h2, ite_false] at h ⊢
          exact ⟨n + 1, 0, by simp [orbit, hx, F, h0, h1, h2], by simp [orbit, hx, F, h0, h1, h2]⟩

/-- From p + 3 = 2^a the odd rule halves p + 3 down to 4, i.e. p = 1. -/
theorem pow2_reaches (a : Nat) : ∀ m, (orbit m).1 + 3 = 2 ^ a → ∃ n, (orbit n).1 = 1 := by
  induction a with
  | zero => intro m h; simp at h
  | succ a ih =>
    intro m h
    by_cases h1 : (orbit m).1 = 1
    · exact ⟨m, h1⟩
    · apply ih (m + 1)
      rw [Nat.pow_succ] at h
      have h0 : (orbit m).1 ≠ 0 := by
        intro e; rw [e] at h
        cases a with
        | zero => simp at h
        | succ a => rw [Nat.pow_succ] at h; omega
      have h2 : (orbit m).1 % 2 = 1 := by omega
      simp only [orbit, F, h0, h1, h2, ite_true, ite_false]
      omega

/-- **The machine halts from blank tape iff some sample K(p, 1) has p + 3 a power of two.** -/
theorem halts_iff_pow2 : HaltsFromBlank ↔ ∃ n a, (orbit n).2 = 1 ∧ (orbit n).1 + 3 = 2 ^ a := by
  rw [halts_iff]
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨m, b, hm, hb⟩ := odd_from_q1 n (by rw [hn])
    exact ⟨m, b + 2, hm, by rw [hb, hn, Nat.pow_add]⟩
  · rintro ⟨n, a, -, h⟩
    exact pow2_reaches a n h

/-- A run that halts after `N` steps (the halting step not counted) passed every sample: `time n < N` for all n
(even for samples with p = 1, which still take six steps to halt). -/
theorem time_lt_of_halts {N : Nat} {c : Config} (hN : steps N init = some c) (hc : step c = none)
    (n : Nat) : time n < N := by
  have hr := reach n
  refine Nat.lt_of_not_le fun hle => ?_
  -- if N ≤ time n, the run to time n passes the halting configuration c
  obtain ⟨d, hd⟩ : ∃ d, time n = N + d := ⟨time n - N, by omega⟩
  rw [hd] at hr
  cases d with
  | zero =>
    rw [Nat.add_zero, hN] at hr
    cases hr
    -- c = K p q does not halt at once: the head reads 0 in state A
    exact absurd hc (by simp [step, TM.step, K, trans, cons])
  | succ d =>
    have h' : steps (N + (d + 1)) init = none := steps_halt trans hN hc d
    rw [h'] at hr
    cases hr

end H31371
