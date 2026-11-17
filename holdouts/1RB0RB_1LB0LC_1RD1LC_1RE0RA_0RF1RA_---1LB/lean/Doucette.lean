import Map

/-!
# 1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB: Doucette's form in base 3

Sample the hole map of `Map.lean` at the samples `S(p, r)` that start a run of divisions, and write
`D = p + 1 = 3^v · (3a + ρ)` with ρ ∈ {1, 2}.  A run of v division steps `p ↦ (p − 2)/3` takes `D` to `3a + ρ`, and
the step that ends it gives the next start (`G`):

* `(D, r) ↦ (D + a + v + r + ρ + 1, 1)` (`G_rule`, when `D` is not a power of 3).  On the samples with r = 1 this is
  `D ↦ D + a + v + 2 + ρ`: the base-3 version of Doucette's form (Space Needle's is `D + 3a + v` in base 2,
  `holdouts/1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD/lean/Collatz.lean`);
* `D = 3^v`: the run ends at the special case p = 2, which **halts iff v + r ≡ 1 (mod 3)** and otherwise goes on to
  `(D + v + r + 2, 1)` or `(D + v + r, 2)` (`G_pow3`).  This never happens in the first 5,000 samples.

`halts_iff_doucette`: **the machine halts from blank tape iff the sequence (4, 1), (8, 1), (14, 1), (22, 1), ... of
`Dorb` reaches a pair `(3^v, r)` with v + r ≡ 1 (mod 3)**.  With r = 1 that is a power `3^v` with `3 ∣ v`: not every
power of 3 halts.
-/

namespace H86694

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

/-! ## The hole map as a partial map -/

/-- One step of the hole map. -/
def nf (x : Nat × Nat) : Option (Nat × Nat) := f x.1 x.2

theorem orb_oit (n : Nat) : orb n = oit nf n (some (3, 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [oit_succ', ← ih]
    show (match orb n with | some (p, r) => f p r | none => none) = _
    cases orb n <;> rfl

/-! ## Runs of divisions -/

theorem nf_div (x r : Nat) (hx : 2 ≤ x) : nf (3 * x - 1, r) = some (x - 1, 2 * x + r + 1) := by
  simp only [nf, f, show 3 * x - 1 ≠ 1 by omega, show 3 * x - 1 ≠ 2 by omega, show (3 * x - 1) % 3 ≠ 0 by omega,
    show (3 * x - 1) % 3 ≠ 1 by omega, ite_false, Option.some.injEq, Prod.mk.injEq]
  omega

/-- `j` divisions: `S(3^j E − 1, r)` leads to `S(E − 1, r + j + 3^j E − E)`. -/
theorem chain (E : Nat) (hE : 2 ≤ E) (j : Nat) : ∀ r,
    oit nf j (some (3 ^ j * E - 1, r)) = some (E - 1, r + j + (3 ^ j * E - E)) := by
  induction j with
  | zero => intro r; simp [oit]
  | succ j ih =>
    intro r
    have hx : E ≤ 3 ^ j * E := Nat.le_mul_of_pos_left E (Nat.pow_pos (by omega))
    have e3 : 3 ^ (j + 1) * E = 3 * (3 ^ j * E) := by
      rw [Nat.pow_succ, Nat.mul_comm (3 ^ j) 3, Nat.mul_assoc]
    rw [e3]
    generalize hxd : 3 ^ j * E = x at hx ih ⊢
    show oit nf j (nf (3 * x - 1, r)) = _
    rw [nf_div x r (by omega), ih]
    congr 2; omega

/-! ## Doucette's map -/

/-- The map on `(D, r) = (p + 1, r)` at the starts of the runs of divisions; `none` when the machine halts. -/
def G (x : Nat × Nat) : Option (Nat × Nat) :=
  if part 3 x.1 = 1 then
    (if (val 3 x.1 + x.2) % 3 = 1 then none
     else if (val 3 x.1 + x.2) % 3 = 2 then some (x.1 + val 3 x.1 + x.2 + 2, 1)
     else some (x.1 + val 3 x.1 + x.2, 2))
  else some (x.1 + part 3 x.1 / 3 + val 3 x.1 + x.2 + part 3 x.1 % 3 + 1, 1)

/-- The samples: `(D, r)` stands for `S(D − 1, r)`. -/
def e (x : Nat × Nat) : Nat × Nat := (x.1 - 1, x.2)

/-- The invariant: `D ≥ 2`, `r ≥ 1`. -/
def I (x : Nat × Nat) : Prop := 2 ≤ x.1 ∧ 1 ≤ x.2

/-- Doucette's sequence of this machine: (4, 1), (8, 1), (14, 1), (22, 1), (32, 1), (46, 1), ... -/
def Dorb (k : Nat) : Option (Nat × Nat) := oit G k (some (4, 1))

theorem G_inv (x y : Nat × Nat) (hx : I x) (h : G x = some y) : I y := by
  obtain ⟨D, r⟩ := x
  unfold I at hx ⊢
  unfold G at h
  simp only at h hx
  split at h
  · split at h
    · cases h
    · split at h <;> (cases h; simp only; omega)
  · cases h; simp only; omega

theorem G_step (x y : Nat × Nat) (hx : I x) (h : G x = some y) :
    ∃ j, 0 < j ∧ oit nf j (some (e x)) = some (e y) := by
  obtain ⟨D, r⟩ := x
  obtain ⟨hD, hr⟩ := hx
  simp only at hD hr
  obtain ⟨hs, ho⟩ := part_spec 3 D (by omega) (by omega)
  unfold G at h
  simp only at h
  generalize hv : val 3 D = v at hs h
  generalize hE : part 3 D = E at hs ho h
  have hE1 : 1 ≤ E := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at ho; simp at ho)
  have hEle : E ≤ D := by rw [← hs]; exact Nat.le_mul_of_pos_left E (Nat.pow_pos (by omega))
  by_cases h1 : E = 1
  · rw [ite_eq_left h1] at h
    subst h1
    have hv1 : 1 ≤ v := by
      rcases Nat.eq_zero_or_pos v with h0 | h0
      · subst h0; simp at hs; omega
      · exact h0
    have e3 : D = 3 ^ (v - 1) * 3 := by
      have : 3 ^ v = 3 ^ (v - 1) * 3 := by rw [← Nat.pow_succ]; congr 1; omega
      rw [this] at hs; omega
    have hD3 : D % 3 = 0 := by omega
    have hc := chain 3 (by omega) (v - 1) r
    rw [← e3] at hc
    refine ⟨v - 1 + 1, by omega, ?_⟩
    unfold e
    rw [oit_add, hc]
    show nf (2, r + (v - 1) + (D - 3)) = _
    simp only [nf, f, show (2 : Nat) ≠ 1 by omega, ite_false, ite_true]
    by_cases h31 : (v + r) % 3 = 1
    · rw [ite_eq_left h31] at h; cases h
    rw [ite_eq_right h31] at h
    by_cases h32 : (v + r) % 3 = 2
    · rw [ite_eq_left h32] at h; cases h
      rw [ite_eq_left (show (r + (v - 1) + (D - 3)) % 3 = 1 by omega)]
      congr 2; omega
    · rw [ite_eq_right h32] at h; cases h
      rw [ite_eq_right (show ¬ (r + (v - 1) + (D - 3)) % 3 = 1 by omega),
        ite_eq_left (show (r + (v - 1) + (D - 3)) % 3 = 2 by omega)]
      congr 2; omega
  · rw [ite_eq_right h1] at h; cases h
    have hE2 : 2 ≤ E := by omega
    have hc := chain E hE2 v r
    rw [hs] at hc
    refine ⟨v + 1, by omega, ?_⟩
    unfold e
    rw [oit_add, hc]
    show nf (E - 1, r + v + (D - E)) = _
    by_cases hρ : E % 3 = 1
    · simp only [nf, f, show E - 1 ≠ 1 by omega, show E - 1 ≠ 2 by omega, show (E - 1) % 3 = 0 by omega,
        ite_false, ite_true, Option.some.injEq, Prod.mk.injEq, and_true]
      omega
    · have hρ2 : E % 3 = 2 := by omega
      by_cases ha : E = 2
      · subst ha
        simp only [nf, f, ite_true, Option.some.injEq, Prod.mk.injEq, and_true]
        omega
      · simp only [nf, f, show E - 1 ≠ 1 by omega, show E - 1 ≠ 2 by omega, show (E - 1) % 3 = 1 by omega,
          ite_false]
        rw [ite_eq_right (by decide)]
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq, and_true]
        omega

theorem G_halt (x : Nat × Nat) (hx : I x) (h : G x = none) : ∃ j, oit nf j (some (e x)) = none := by
  obtain ⟨D, r⟩ := x
  obtain ⟨hD, hr⟩ := hx
  simp only at hD hr
  obtain ⟨hs, _⟩ := part_spec 3 D (by omega) (by omega)
  unfold G at h
  simp only at h
  by_cases hE : part 3 D = 1
  · rw [ite_eq_left hE] at h
    rw [hE, Nat.mul_one] at hs
    generalize hv : val 3 D = v at hs h
    by_cases h31 : (v + r) % 3 = 1
    · have hv1 : 1 ≤ v := by
        rcases Nat.eq_zero_or_pos v with h0 | h0
        · subst h0; simp at hs; omega
        · exact h0
      have e3 : D = 3 ^ (v - 1) * 3 := by
        have : 3 ^ v = 3 ^ (v - 1) * 3 := by rw [← Nat.pow_succ]; congr 1; omega
        rw [this] at hs; omega
      have hc := chain 3 (by omega) (v - 1) r
      rw [← e3] at hc
      refine ⟨v - 1 + 1, ?_⟩
      unfold e
      rw [oit_add, hc]
      show nf (2, r + (v - 1) + (D - 3)) = none
      simp only [nf, f, show (2 : Nat) ≠ 1 by omega, ite_false, ite_true,
        show ¬ (r + (v - 1) + (D - 3)) % 3 = 1 by omega, show ¬ (r + (v - 1) + (D - 3)) % 3 = 2 by omega]
    · rw [ite_eq_right h31] at h
      split at h <;> cases h
  · rw [ite_eq_right hE] at h; cases h

/-- **The halting problem in Doucette's form**: the machine halts from blank tape iff `Dorb` ends. -/
theorem halts_iff_Dorb : HaltsFromBlank ↔ ∃ k, Dorb k = none := by
  rw [halts_iff]
  simp only [orb_oit]
  exact accel nf G e I (3, 1) (4, 1) 0 rfl ⟨by decide, by decide⟩ G_inv G_step G_halt

/-- **The machine halts from blank tape iff Doucette's sequence (4, 1), (8, 1), (14, 1), ... reaches a pair
`(3^v, r)` with v + r ≡ 1 (mod 3).** -/
theorem halts_iff_doucette : HaltsFromBlank ↔ ∃ k v r, Dorb k = some (3 ^ v, r) ∧ (v + r) % 3 = 1 := by
  rw [halts_iff_Dorb]; unfold Dorb; rw [oit_none_iff]
  constructor
  · rintro ⟨k, ⟨D, r⟩, hk, hD⟩
    unfold G at hD
    simp only at hD
    by_cases hp : part 3 D = 1
    · rw [ite_eq_left hp] at hD
      have hD0 : D ≠ 0 := by
        intro h0; subst h0; simp [part, val, vf] at hp
      have := (part_spec 3 D (by omega) hD0).1
      rw [hp, Nat.mul_one] at this
      refine ⟨k, val 3 D, r, by rw [hk, this], ?_⟩
      by_cases h31 : (val 3 D + r) % 3 = 1
      · exact h31
      · rw [ite_eq_right h31] at hD; split at hD <;> cases hD
    · rw [ite_eq_right hp] at hD; cases hD
  · rintro ⟨k, v, r, hk, h31⟩
    refine ⟨k, _, hk, ?_⟩
    obtain ⟨h1, h2⟩ := val_part 3 (by omega) v 1 (by omega)
    rw [Nat.mul_one] at h1 h2
    simp [G, h1, h2, h31]

/-! ## The rule in closed form -/

/-- **Doucette's rule in base 3**: `(3^v (3a + ρ), r) ↦ (3^v (3a + ρ) + a + v + r + ρ + 1, 1)` for ρ ∈ {1, 2},
`3a + ρ ≥ 2`. -/
theorem G_rule (v a ρ r : Nat) (hρ : ρ = 1 ∨ ρ = 2) (h2 : 2 ≤ 3 * a + ρ) :
    G (3 ^ v * (3 * a + ρ), r) = some (3 ^ v * (3 * a + ρ) + a + v + r + ρ + 1, 1) := by
  obtain ⟨h1, h2'⟩ := val_part 3 (by omega) v (3 * a + ρ) (by omega)
  simp only [G, h1, h2', show 3 * a + ρ ≠ 1 by omega, ite_false, Option.some.injEq, Prod.mk.injEq, and_true]
  omega

/-- A power of 3: halt iff v + r ≡ 1 (mod 3). -/
theorem G_pow3 (v r : Nat) : G (3 ^ v, r) =
    if (v + r) % 3 = 1 then none
    else if (v + r) % 3 = 2 then some (3 ^ v + v + r + 2, 1) else some (3 ^ v + v + r, 2) := by
  obtain ⟨h1, h2⟩ := val_part 3 (by omega) v 1 (by omega)
  rw [Nat.mul_one] at h1 h2
  simp [G, h1, h2]

theorem Dorb_start : Dorb 9 = some (137, 1) := by decide

end H86694
