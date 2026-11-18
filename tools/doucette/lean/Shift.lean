/-!
# The shift identity behind the fast orbit computation (`tools/doucette/djump.py`)

All five Doucette maps have, away from their exceptional values, the form

    step D = D + α · (part D / b) + β (val D) (part D % b),      D = b^(val D) · part D,  b ∤ part D

(Space Needle: b = 2, α = 3, β v ρ = v; the others: α = 1 and β v ρ = v + γ, or base 3 with β v ρ = v + ρ + 2).

**`shift`**: if `D = b^m · X + L` with `X ≥ 1`, `L ≠ 0` and `val L + 2 ≤ m`, then `D` has the same valuation and
the same last digit of its part as `L`, its part is at least `b^2` (so `D` is not exceptional), and

    step D = b^(m − v − 1) · (b^(v+1) + α) · X + step L,       v = val L.

**`jump`**: iterating, as long as each low part `L_i` keeps `val L_i + 2 ≤ m − s_i`,

    step^k (b^m X + L) = b^(m − s_k) · c_k · X + step^k L,     s_k = Σ (v_i + 1),  c_k = Π (b^(v_i+1) + α),

so the next k valuations depend only on the low part `L`, and the algorithm can advance the low digits
alone and fold the high part back in with one multiplication.  No exceptional value (a power of b, or part 3 in
base 2) occurs inside a jump.
-/

namespace Shift

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


/-- The generic Doucette step. -/
def step (b α : Nat) (β : Nat → Nat → Nat) (D : Nat) : Nat :=
  D + α * (part b D / b) + β (val b D) (part b D % b)

theorem pow_split (b m v : Nat) (h : v + 1 ≤ m) : b ^ m = b ^ (m - v - 1) * b ^ (v + 1) := by
  rw [← Nat.pow_add]; congr 1; omega

/-- **The shift identity.** -/
theorem shift (b α : Nat) (β : Nat → Nat → Nat) (hb : 2 ≤ b) (m X L : Nat) (hX : 1 ≤ X) (hL : L ≠ 0)
    (hv : val b L + 2 ≤ m) :
    val b (b ^ m * X + L) = val b L ∧ part b (b ^ m * X + L) % b = part b L % b ∧
    b ^ 2 ≤ part b (b ^ m * X + L) ∧
    step b α β (b ^ m * X + L) = b ^ (m - val b L - 1) * (b ^ (val b L + 1) + α) * X + step b α β L := by
  obtain ⟨hs, ho⟩ := part_spec b L hb hL
  generalize hvv : val b L = v at hs hv ⊢
  generalize hE : part b L = E at hs ho ⊢
  -- b^m X + L = b^v (b^(m-v) X + E)
  have hm : b ^ m = b ^ v * b ^ (m - v) := by rw [← Nat.pow_add]; congr 1; omega
  have hmv : b ^ (m - v) = b * b ^ (m - v - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hD : b ^ m * X + L = b ^ v * (b ^ (m - v) * X + E) := by
    rw [hm, Nat.mul_add, ← hs, Nat.mul_assoc]
  have hE' : (b ^ (m - v) * X + E) % b = E % b := by
    rw [hmv, Nat.mul_assoc, Nat.mul_add_mod]
  obtain ⟨h1, h2⟩ := val_part b hb v (b ^ (m - v) * X + E) (by rw [hE']; exact ho)
  rw [hD, h1, h2, hE']
  refine ⟨rfl, rfl, ?_, ?_⟩
  · have : b ^ 2 ≤ b ^ (m - v) := Nat.pow_le_pow_right (by omega) (by omega)
    have : b ^ (m - v) ≤ b ^ (m - v) * X := Nat.le_mul_of_pos_right _ hX
    omega
  · have hdiv : (b ^ (m - v) * X + E) / b = b ^ (m - v - 1) * X + E / b := by
      rw [hmv, Nat.mul_assoc, Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.add_comm]
    unfold step
    rw [hvv, hE, h1, h2, hdiv, hE', ← hD]
    have hb1 : b ^ (m - v - 1) * (b ^ (v + 1) + α) * X = b ^ m * X + α * (b ^ (m - v - 1) * X) := by
      rw [pow_split b m v (by omega), Nat.mul_add, Nat.add_mul, Nat.mul_comm (b ^ (m - v - 1)) (b ^ (v + 1))]
      rw [Nat.mul_assoc (b ^ (v + 1)), Nat.mul_assoc (b ^ (m - v - 1)) α, Nat.mul_comm α X,
        ← Nat.mul_assoc (b ^ (m - v - 1)) X α, Nat.mul_comm _ α]
    rw [hb1, Nat.mul_add]
    omega

/-- `iter f k x`: `k` applications of `f`. -/
def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => f (iter f k x)

/-- The low-part iteration: `(L_k, s_k, c_k)` after `k` steps from `L`. -/
def low (b α : Nat) (β : Nat → Nat → Nat) : Nat → Nat → Nat × Nat × Nat
  | 0, L => (L, 0, 1)
  | k + 1, L =>
    let r := low b α β k L
    (step b α β r.1, r.2.1 + (val b r.1 + 1), r.2.2 * (b ^ (val b r.1 + 1) + α))

/-- `k` steps are certain from the trusted window `m`: every low part is nonzero and has `val + 2` below the
remaining window. -/
def certain (b α : Nat) (β : Nat → Nat → Nat) (m L : Nat) (k : Nat) : Prop :=
  ∀ i < k, (low b α β i L).1 ≠ 0 ∧ val b (low b α β i L).1 + 2 + (low b α β i L).2.1 ≤ m

/-- **The jump.**  If `k` steps are certain, then `k` steps of the full value are the low iteration with the high
part multiplied in, and none of the full values met on the way is exceptional (`part ≥ b^2`). -/
theorem jump (b α : Nat) (β : Nat → Nat → Nat) (hb : 2 ≤ b) (m X L : Nat) (hX : 1 ≤ X) :
    ∀ k, certain b α β m L k →
      (low b α β k L).2.1 ≤ m ∧
      iter (step b α β) k (b ^ m * X + L) =
        b ^ (m - (low b α β k L).2.1) * ((low b α β k L).2.2 * X) + (low b α β k L).1 ∧
      ∀ i < k, b ^ 2 ≤ part b (iter (step b α β) i (b ^ m * X + L)) := by
  intro k
  induction k with
  | zero => intro _; simp [low, iter]
  | succ k ih =>
    intro hc
    have hck : certain b α β m L k := fun i hi => hc i (by omega)
    obtain ⟨hs, hit, hex⟩ := ih hck
    obtain ⟨hL0, hw⟩ := hc k (by omega)
    generalize hr : low b α β k L = r at hs hit hex hL0 hw
    obtain ⟨Lk, sk, ck⟩ := r
    simp only at hs hit hL0 hw
    have hck1 : 1 ≤ ck * X := by
      have : ∀ j, 1 ≤ (low b α β j L).2.2 := by
        intro j
        induction j with
        | zero => simp [low]
        | succ j ihj =>
          simp only [low]
          exact Nat.mul_pos ihj (by have := Nat.pow_pos (n := val b (low b α β j L).1 + 1) (show 0 < b by omega); omega)
      have := this k; rw [hr] at this; exact Nat.mul_pos this hX
    obtain ⟨_, _, hpart, hstep⟩ := shift b α β hb (m - sk) (ck * X) Lk hck1 hL0 (by omega)
    refine ⟨?_, ?_, ?_⟩
    · simp only [low, hr]; omega
    · show step b α β (iter (step b α β) k _) = _
      rw [hit, hstep]
      simp only [low, hr]
      have e : m - sk - val b Lk - 1 = m - (sk + (val b Lk + 1)) := by omega
      rw [e, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm (b ^ (val b Lk + 1) + α) (ck * X), ← Nat.mul_assoc ck]
      rw [Nat.mul_comm ck, Nat.mul_assoc, Nat.mul_comm X]
    · intro i hi
      by_cases hik : i < k
      · exact hex i hik
      · have : i = k := by omega
        subst this
        rw [hit]; exact hpart

end Shift
