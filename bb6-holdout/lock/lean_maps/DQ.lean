/-! # The quadratic lock of the pass map Q

`D` is the integer quadratic of `../DQ.txt` (variables w2, w3, w4, E).  `D_Q`: whenever the image of Q is integral,
`4096 · D(Q x) = D(x)`.  `D_ne_zero`: `D` has no integer zero, because `314961784 · D = A² − 17 B²` with integer affine
`A`, `B` (`D_AB`), `A² = 17 B²` forces `A = B = 0` (`sq17`, by descent), and `A = B = 0` has no integer solution. -/

def D (w2 w3 w4 E : Int) : Int :=
  -58529536*E*E + 88773450*E*w2 - 82739064*E*w3 + 155524704*E*w4 - 148647028*E - 12044232*w2*w2 + 7527645*w2*w3 - 85313310*w2*w4 - 9620823*w2 + 6022116*w3*w3 + 68250648*w3*w4 + 51198954*w3 - 91000864*w4*w4 + 105148876*w4 + 78740446

def DA (w2 w3 w4 E : Int) : Int := -148647028*E - 9620823*w2 + 51198954*w3 + 105148876*w4 + 157480892
def DB (w2 w3 w4 E : Int) : Int := -48827732*E + 15119199*w2 - 6528654*w3 + 48335884*w4

theorem D_Q (w2 w3 w4 E a b c e : Int) (ha : 128 * a = 9 * w2 + 4 * w3 + 16 * w4 + 32 * E + 1710)
    (hb : 32 * b = 2 * w2 + w3 + 6 * w4 + 22 * E + 701) (hc : 16 * c = w4 + 15 * E + 369) (he : e = E + 24) :
    4096 * D a b c e = D w2 w3 w4 E := by
  unfold D; grind

theorem D_AB (w2 w3 w4 E : Int) : 314961784 * D w2 w3 w4 E = DA w2 w3 w4 E * DA w2 w3 w4 E - 17 * (DB w2 w3 w4 E * DB w2 w3 w4 E) := by
  unfold D DA DB; grind

theorem sq_mod17 (a : Int) (h : (a * a) % 17 = 0) : a % 17 = 0 := by
  have hm : (a * a) % 17 = ((a % 17) * (a % 17)) % 17 := Int.mul_emod a a 17
  have h0 : 0 ≤ a % 17 := Int.emod_nonneg a (by decide)
  have h1 : a % 17 < 17 := Int.emod_lt_of_pos a (by decide)
  generalize a % 17 = r at hm h0 h1 ⊢
  rw [hm] at h
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨
    r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 ∨ r = 16 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all

/-- `√17` is irrational, in the form needed: `a² = 17 b²` over the integers forces `b = 0`. -/
theorem sq17 : ∀ (n : Nat) (a b : Int), b.natAbs = n → a * a = 17 * (b * b) → b = 0 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro a b hn h
    have ha : a % 17 = 0 := sq_mod17 a (by rw [h]; simp [Int.mul_emod_right])
    obtain ⟨q, rfl⟩ : ∃ q, a = 17 * q := ⟨a / 17, by omega⟩
    have hb2 : b * b = 17 * (q * q) := by
      have : 17 * (17 * (q * q)) = 17 * (b * b) := by rw [← h]; grind
      omega
    have hb : b % 17 = 0 := sq_mod17 b (by rw [hb2]; simp [Int.mul_emod_right])
    obtain ⟨p, rfl⟩ : ∃ p, b = 17 * p := ⟨b / 17, by omega⟩
    have hq2 : q * q = 17 * (p * p) := by
      have : 17 * (17 * (p * p)) = 17 * (q * q) := by rw [← hb2]; grind
      omega
    by_cases hp : p = 0
    · simp [hp]
    · have := ih p.natAbs (by rw [← hn, Int.natAbs_mul]; have := Int.natAbs_pos.mpr hp; simp; omega) q p rfl hq2
      exact absurd this hp

theorem AB_no_int_zero (w2 w3 w4 E : Int) (hA : DA w2 w3 w4 E = 0) (hB : DB w2 w3 w4 E = 0) : False := by
  unfold DA at hA; unfold DB at hB; omega

/-- **`D` has no integer zero.** -/
theorem D_ne_zero (w2 w3 w4 E : Int) : D w2 w3 w4 E ≠ 0 := by
  intro hD
  have h := D_AB w2 w3 w4 E
  rw [hD, Int.mul_zero] at h
  have hB : DB w2 w3 w4 E = 0 := sq17 _ (DA w2 w3 w4 E) (DB w2 w3 w4 E) rfl (by omega)
  have hA : DA w2 w3 w4 E * DA w2 w3 w4 E = 0 := by rw [hB] at h; omega
  exact AB_no_int_zero w2 w3 w4 E (by rcases Int.mul_eq_zero.mp hA with h | h <;> exact h) hB

#print axioms D_Q
#print axioms D_ne_zero
