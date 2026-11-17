import Reduction

/-!
# 1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE: Doucette's form

Sample the run at the configurations `K(p, 1)` and write `D = p + 3 = 2^v · (2a + 1)`.  Between two such samples the
odd rule of `Reduction.lean` halves `D` v times and the even rule ends the run of halvings, so the next sample has

* `D' = D + a + v` (`G_rule`, for a ≥ 2): the same form as Space Needle's `D + 3a + v`
  (`holdouts/1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD/lean/Collatz.lean`), with the factor 3 replaced by 1;
* `D' = D + v + 3` when `D = 3 · 2^v` (`G_three`; the general rule would give `D + v + 1`; this value never occurs in
  the first 5,000 samples);
* a halt when `D` is a power of two (`G_pow2`).

`halts_iff_doucette`: **the machine halts from blank tape iff the sequence 5, 7, 10, 13, 19, 28, ... of `Dorb` reaches a
power of two.**
-/

namespace H31371

/-! ## Iterating a partial map -/

/-- `oit f n o`: `n` steps of the partial map `f` from `o`; `none` (halted) stays `none`. -/
def oit {α : Type} (f : α → Option α) : Nat → Option α → Option α
  | 0, o => o
  | n + 1, o => oit f n (o.bind f)

theorem oit_none {α : Type} (f : α → Option α) (n : Nat) : oit f n none = none := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem oit_add {α : Type} (f : α → Option α) (n m : Nat) (o : Option α) :
    oit f (n + m) o = oit f m (oit f n o) := by
  induction n generalizing o with
  | zero => simp [oit]
  | succ n ih => rw [show n + 1 + m = (n + m) + 1 by omega]; exact ih _

theorem oit_succ' {α : Type} (f : α → Option α) (n : Nat) (o : Option α) :
    oit f (n + 1) o = (oit f n o).bind f := by
  rw [oit_add f n 1]; cases oit f n o <;> rfl

theorem oit_none_le {α : Type} (f : α → Option α) {n m : Nat} {o : Option α} (h : oit f n o = none)
    (hm : n ≤ m) : oit f m o = none := by
  obtain ⟨d, rfl⟩ : ∃ d, m = n + d := ⟨m - n, by omega⟩
  rw [oit_add, h, oit_none]

/-- **Acceleration.** Let `G` jump from one sample `e y` of the orbit of `f` to a later one `e y'` (at least one step
later), and return `none` exactly where `f` halts in between.  Then the orbit of `f` from `x0` halts iff the orbit of
`G` from `y0` does. -/
theorem accel {α β : Type} (f : α → Option α) (G : β → Option β) (e : β → α) (I : β → Prop)
    (x0 : α) (y0 : β) (n0 : Nat) (h0 : oit f n0 (some x0) = some (e y0)) (hI0 : I y0)
    (hI : ∀ y y', I y → G y = some y' → I y')
    (hs : ∀ y y', I y → G y = some y' → ∃ j, 0 < j ∧ oit f j (some (e y)) = some (e y'))
    (hh : ∀ y, I y → G y = none → ∃ j, oit f j (some (e y)) = none) :
    (∃ n, oit f n (some x0) = none) ↔ ∃ k, oit G k (some y0) = none := by
  have reach : ∀ k y, oit G k (some y0) = some y → I y ∧ ∃ t, k ≤ t ∧ oit f t (some x0) = some (e y) := by
    intro k
    induction k with
    | zero => intro y h; cases h; exact ⟨hI0, n0, Nat.zero_le _, h0⟩
    | succ k ih =>
      intro y h
      rw [oit_succ'] at h
      cases hk : oit G k (some y0) with
      | none => rw [hk] at h; cases h
      | some z =>
        rw [hk] at h
        obtain ⟨hz, t, ht, hft⟩ := ih z hk
        obtain ⟨j, hj, hfj⟩ := hs z y hz h
        exact ⟨hI z y hz h, t + j, by omega, by rw [oit_add, hft, hfj]⟩
  constructor
  · rintro ⟨n, hn⟩
    refine Classical.byContradiction fun hno => ?_
    cases hk : oit G (n + 1) (some y0) with
    | none => exact hno ⟨_, hk⟩
    | some y =>
      obtain ⟨_, t, ht, hft⟩ := reach _ y hk
      rw [oit_none_le f hn (by omega : n ≤ t)] at hft
      cases hft
  · rintro ⟨k, hk⟩
    induction k with
    | zero => cases hk
    | succ k ih =>
      rw [oit_succ'] at hk
      cases hk' : oit G k (some y0) with
      | none => exact ih hk'
      | some z =>
        rw [hk'] at hk
        obtain ⟨hz, t, -, hft⟩ := reach k z hk'
        obtain ⟨j, hfj⟩ := hh z hz hk
        exact ⟨t + j, by rw [oit_add, hft, hfj]⟩

/-- An orbit of a partial map ends iff it reaches a point where the map is `none`. -/
theorem oit_none_iff {β : Type} (G : β → Option β) (y0 : β) :
    (∃ k, oit G k (some y0) = none) ↔ ∃ k y, oit G k (some y0) = some y ∧ G y = none := by
  constructor
  · rintro ⟨k, hk⟩
    induction k with
    | zero => cases hk
    | succ k ih =>
      rw [oit_succ'] at hk
      cases hk' : oit G k (some y0) with
      | none => exact ih hk'
      | some z => rw [hk'] at hk; exact ⟨k, z, hk', hk⟩
  · rintro ⟨k, y, hk, hy⟩
    exact ⟨k + 1, by rw [oit_succ', hk]; exact hy⟩

/-! ## Valuations -/

/-- `vf b fuel n`: the number of factors `b` of `n` (for `n ≤ fuel`). -/
def vf (b : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => if n ≠ 0 ∧ n % b = 0 then vf b f (n / b) + 1 else 0

/-- The `b`-adic valuation `v` of `n`. -/
def val (b n : Nat) : Nat := vf b n n

/-- The part of `n` prime to `b`: `n = b ^ val b n * part b n`. -/
def part (b n : Nat) : Nat := n / b ^ val b n

theorem vf_spec (b : Nat) (hb : 2 ≤ b) : ∀ (f n : Nat), n ≠ 0 → n ≤ f →
    b ^ vf b f n * (n / b ^ vf b f n) = n ∧ (n / b ^ vf b f n) % b ≠ 0 := by
  intro f
  induction f with
  | zero => intro n h0 hf; omega
  | succ f ih =>
    intro n h0 hf
    by_cases h : n % b = 0
    · have hv : vf b (f + 1) n = vf b f (n / b) + 1 := by simp [vf, h0, h]
      have hq : b * (n / b) = n := by have := Nat.div_add_mod n b; omega
      have h2 : n / b ≠ 0 := by intro e; rw [e] at hq; omega
      have h3 : n / b ≤ f := by
        have : n / b < n := Nat.div_lt_self (by omega) (by omega)
        omega
      obtain ⟨ih1, ih2⟩ := ih (n / b) h2 h3
      rw [hv]
      have e : n / b ^ (vf b f (n / b) + 1) = n / b / b ^ vf b f (n / b) := by
        rw [Nat.pow_succ, Nat.mul_comm, Nat.div_div_eq_div_mul]
      rw [e]
      refine ⟨?_, ih2⟩
      rw [Nat.pow_succ, Nat.mul_comm (b ^ _) b, Nat.mul_assoc, ih1, hq]
    · have hv : vf b (f + 1) n = 0 := by simp [vf, h]
      rw [hv]; simp; exact h

theorem part_spec (b n : Nat) (hb : 2 ≤ b) (h : n ≠ 0) : b ^ val b n * part b n = n ∧ part b n % b ≠ 0 :=
  vf_spec b hb n n h (Nat.le_refl n)

theorem vf_unique (b : Nat) (hb : 2 ≤ b) (E : Nat) (hE : E % b ≠ 0) :
    ∀ v f, b ^ v * E ≤ f → vf b f (b ^ v * E) = v := by
  have hE0 : E ≠ 0 := by intro h; rw [h] at hE; simp at hE
  intro v
  induction v with
  | zero =>
    intro f hf
    cases f with
    | zero => simp at hf; omega
    | succ f => simp [vf, hE]
  | succ v ih =>
    intro f hf
    have hp : 0 < b ^ v := Nat.pow_pos (by omega)
    have hpos : 0 < b ^ v * E := Nat.mul_pos hp (by omega)
    have e : b ^ (v + 1) * E = b * (b ^ v * E) := by rw [Nat.pow_succ, Nat.mul_comm (b ^ v) b, Nat.mul_assoc]
    rw [e] at hf ⊢
    cases f with
    | zero => have : 0 < b * (b ^ v * E) := Nat.mul_pos (by omega) hpos; omega
    | succ f =>
      have h1 : b * (b ^ v * E) ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (by omega) hpos)
      have h2 : b * (b ^ v * E) % b = 0 := Nat.mul_mod_right _ _
      have h3 : b * (b ^ v * E) / b = b ^ v * E := Nat.mul_div_cancel_left _ (by omega)
      simp only [vf, h1, h2, ne_eq, not_false_eq_true, and_self, ite_true, h3]
      rw [ih f (by have : b ^ v * E < b * (b ^ v * E) := by
                     have := Nat.mul_lt_mul_of_pos_right (show 1 < b by omega) hpos; omega
                   omega)]

/-- `val` and `part` of `b ^ v * E` with `b ∤ E` are `v` and `E`. -/
theorem val_part (b : Nat) (hb : 2 ≤ b) (v E : Nat) (hE : E % b ≠ 0) :
    val b (b ^ v * E) = v ∧ part b (b ^ v * E) = E := by
  have hv : val b (b ^ v * E) = v := vf_unique b hb E hE v _ (Nat.le_refl _)
  refine ⟨hv, ?_⟩
  unfold part; rw [hv]; exact Nat.mul_div_cancel_left E (Nat.pow_pos (by omega))

/-! ## The native map as a partial map -/

/-- One sample step of `Reduction.lean`; `none` at p = 1, where the machine halts. -/
def nf (x : Nat × Nat) : Option (Nat × Nat) := if x.1 = 1 then none else some (F x)

theorem native_aux (n : Nat) : ((∀ i < n, (orbit i).1 ≠ 1) → oit nf n (some (0, 2)) = some (orbit n)) ∧
    ((∃ i < n, (orbit i).1 = 1) → oit nf n (some (0, 2)) = none) := by
  induction n with
  | zero => exact ⟨fun _ => rfl, fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [oit_succ']
    refine ⟨fun h => ?_, fun ⟨i, hi, h1⟩ => ?_⟩
    · rw [ih1 (fun i hi => h i (by omega))]
      show nf (orbit n) = some (F (orbit n))
      simp [nf, h n (by omega)]
    · by_cases hb : ∃ i < n, (orbit i).1 = 1
      · rw [ih2 hb]; rfl
      · have hin : i = n := by
          refine Nat.le_antisymm (by omega) (Nat.not_lt.mp fun hlt => hb ⟨i, hlt, h1⟩)
        subst hin
        rw [ih1 (fun j hj e => hb ⟨j, hj, e⟩)]
        show nf (orbit i) = none
        simp [nf, h1]

theorem native_iff : (∃ n, (orbit n).1 = 1) ↔ ∃ n, oit nf n (some (0, 2)) = none := by
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n + 1, (native_aux (n + 1)).2 ⟨n, by omega, hn⟩⟩
  · rintro ⟨n, hn⟩
    refine Classical.byContradiction fun hno => ?_
    rw [(native_aux n).1 (fun i _ e => hno ⟨i, e⟩)] at hn
    cases hn

/-! ## Runs of halvings -/

theorem nf_odd (x q : Nat) (hx : 3 ≤ x) : nf (2 * x - 3, q) = some (x - 3, q + x + 1) := by
  simp only [nf, F, show 2 * x - 3 ≠ 1 by omega, show 2 * x - 3 ≠ 0 by omega, show (2 * x - 3) % 2 = 1 by omega,
    ite_false, ite_true, Option.some.injEq, Prod.mk.injEq]
  omega

/-- `j` halvings: `K(2^j E − 3, q)` leads to `K(E − 3, q + j + 2^j E − E)`. -/
theorem chain (E : Nat) (hE : 3 ≤ E) (j : Nat) : ∀ q,
    oit nf j (some (2 ^ j * E - 3, q)) = some (E - 3, q + j + (2 ^ j * E - E)) := by
  induction j with
  | zero => intro q; simp [oit]
  | succ j ih =>
    intro q
    have hx : E ≤ 2 ^ j * E := Nat.le_mul_of_pos_left E (Nat.pow_pos (by omega))
    have e2 : 2 ^ (j + 1) * E = 2 * (2 ^ j * E) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_assoc]
    rw [e2]
    generalize hxd : 2 ^ j * E = x at hx ih ⊢
    show oit nf j (nf (2 * x - 3, q)) = _
    rw [nf_odd x q (by omega), ih]
    congr 2; omega

/-! ## Doucette's map -/

/-- The map on `D = p + 3` at the samples `K(p, 1)`; `none` when the machine halts. -/
def G (D : Nat) : Option Nat :=
  if part 2 D = 1 then none
  else if part 2 D = 3 then some (D + val 2 D + 3)
  else some (D + part 2 D / 2 + val 2 D)

/-- The samples: `D` stands for `K(D − 3, 1)`. -/
def e (D : Nat) : Nat × Nat := (D - 3, 1)

/-- Doucette's sequence of this machine: 5, 7, 10, 13, 19, 28, 33, 49, 73, 109, ... (`none` once it has halted). -/
def Dorb (k : Nat) : Option Nat := oit G k (some 5)

theorem G_ge (D D' : Nat) (h : G D = some D') : D ≤ D' := by
  unfold G at h
  split at h
  · cases h
  · split at h <;> (simp only [Option.some.injEq] at h; omega)

theorem G_step (D D' : Nat) (hD : 5 ≤ D) (h : G D = some D') :
    ∃ j, 0 < j ∧ oit nf j (some (e D)) = some (e D') := by
  obtain ⟨hs, ho⟩ := part_spec 2 D (by omega) (by omega)
  generalize hv : val 2 D = v at hs h
  generalize hE : part 2 D = E at hs ho h
  unfold G at h
  rw [hv, hE] at h
  have hE1 : 1 ≤ E := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at ho; simp at ho)
  have hEle : E ≤ D := by rw [← hs]; exact Nat.le_mul_of_pos_left E (Nat.pow_pos (by omega))
  by_cases h1 : E = 1
  · rw [ite_eq_left h1] at h; cases h
  rw [ite_eq_right h1] at h
  by_cases h3 : E = 3
  · rw [ite_eq_left h3] at h; cases h
    subst h3
    have hc := chain 3 (by omega) v 1
    rw [hs] at hc
    refine ⟨v + 2, by omega, ?_⟩
    unfold e
    rw [oit_add, hc]
    show oit nf 1 (nf (0, 1 + v + (D - 3))) = _
    have : nf (0, 1 + v + (D - 3)) = some (2, v + (D - 3)) := by
      simp [nf, F]; omega
    rw [this]
    show nf (2, v + (D - 3)) = _
    simp [nf, F]
    omega
  · rw [ite_eq_right h3] at h; cases h
    have hE5 : 5 ≤ E := by omega
    have hc := chain E (by omega) v 1
    rw [hs] at hc
    refine ⟨v + 1, by omega, ?_⟩
    unfold e
    rw [oit_add, hc]
    show nf (E - 3, 1 + v + (D - E)) = _
    simp only [nf, F, show E - 3 ≠ 1 by omega, show E - 3 ≠ 0 by omega, show (E - 3) % 2 = 0 by omega,
      ite_false, Option.some.injEq]
    rw [ite_eq_right (by decide)]
    congr 1; omega

theorem G_halt (D : Nat) (hD : 5 ≤ D) (h : G D = none) : ∃ j, oit nf j (some (e D)) = none := by
  obtain ⟨hs, _⟩ := part_spec 2 D (by omega) (by omega)
  have hE : part 2 D = 1 := by
    unfold G at h; split at h
    · assumption
    · split at h <;> cases h
  rw [hE, Nat.mul_one] at hs
  have hv : 3 ≤ val 2 D := by
    rcases Nat.lt_or_ge (val 2 D) 3 with h' | h'
    · have : 2 ^ val 2 D ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    · exact h'
  have e4 : D = 2 ^ (val 2 D - 2) * 4 := by
    rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add, Nat.sub_add_cancel (by omega)]
    exact hs.symm
  have hc := chain 4 (by omega) (val 2 D - 2) 1
  rw [← e4] at hc
  refine ⟨val 2 D - 2 + 1, ?_⟩
  unfold e
  rw [oit_add, hc]
  simp [oit, nf]

/-- **The halting problem in Doucette's form**: the machine halts from blank tape iff `Dorb` ends. -/
theorem halts_iff_Dorb : HaltsFromBlank ↔ ∃ k, Dorb k = none := by
  rw [halts_iff, native_iff]
  exact accel nf G e (fun D => 5 ≤ D) (0, 2) 5 1 rfl (by omega)
    (fun y y' hy h => Nat.le_trans hy (G_ge y y' h)) (fun y y' hy h => G_step y y' hy h)
    (fun y hy h => G_halt y hy h)

/-- **The machine halts from blank tape iff Doucette's sequence 5, 7, 10, 13, ... reaches a power of two.** -/
theorem halts_iff_doucette : HaltsFromBlank ↔ ∃ k v, Dorb k = some (2 ^ v) := by
  rw [halts_iff_Dorb]; unfold Dorb; rw [oit_none_iff]
  constructor
  · rintro ⟨k, D, hk, hD⟩
    refine ⟨k, val 2 D, ?_⟩
    have hp : part 2 D = 1 := by
      unfold G at hD; split at hD
      · assumption
      · split at hD <;> cases hD
    have hD0 : D ≠ 0 := by
      intro h0; subst h0; simp [part, val, vf] at hp
    have := (part_spec 2 D (by omega) hD0).1
    rw [hp, Nat.mul_one] at this
    rw [hk, this]
  · rintro ⟨k, v, hk⟩
    refine ⟨k, _, hk, ?_⟩
    have := (val_part 2 (by omega) v 1 (by omega)).2
    rw [Nat.mul_one] at this
    simp [G, this]

/-! ## The rule in closed form -/

/-- **Doucette's rule**: `2^v (2a + 1) ↦ 2^v (2a + 1) + a + v` for a ≥ 2. -/
theorem G_rule (v a : Nat) (ha : 2 ≤ a) : G (2 ^ v * (2 * a + 1)) = some (2 ^ v * (2 * a + 1) + a + v) := by
  obtain ⟨h1, h2⟩ := val_part 2 (by omega) v (2 * a + 1) (by omega)
  simp only [G, h1, h2, show 2 * a + 1 ≠ 1 by omega, show 2 * a + 1 ≠ 3 by omega, ite_false, Option.some.injEq]
  omega

/-- The exception a = 1: `3 · 2^v ↦ 3 · 2^v + v + 3`. -/
theorem G_three (v : Nat) : G (2 ^ v * 3) = some (2 ^ v * 3 + v + 3) := by
  obtain ⟨h1, h2⟩ := val_part 2 (by omega) v 3 (by omega)
  simp [G, h1, h2]

/-- A power of two halts. -/
theorem G_pow2 (v : Nat) : G (2 ^ v) = none := by
  have := (val_part 2 (by omega) v 1 (by omega)).2
  rw [Nat.mul_one] at this
  simp [G, this]

theorem Dorb_start : Dorb 9 = some 109 := by decide

end H31371
