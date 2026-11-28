import Frame

/-!
# 1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---: the regular counter is a binary number

A regular counter (`Reg`: last block `≡ 1`, every gap `≡ 3 (mod 4)`) is the binary expansion of the number of
sub-rounds left in the current round.  With the bits of that number lowest first, `0^t 1 b ...`, the last block is
`4t + 1` and the zone has one gap `4n - 1` for each run "one bit, then the 1s after it" (`czb`).  `gstep` is the
decrement (`gstep_czb_dec`, `gstep_czb_one`), and a round ends by starting the next one with all bits 0.  Counted from the start,
`cv A` is the counter after `A` steps (`2^m ≤ A < 2^(m+1)`: round `m`, `2^(m+1) - A` sub-rounds left), and

    giter N (cv A) = some (cv (A + N))                                                     (`giter_cv`)

for every `A ≥ 1` and `N`: the counter in closed form.  `czb_split` cuts a counter at a 0 bit into the gaps of the
low bits and the gaps of the high bits, the form in which the transient after a rebuild reads it (`Map.lean`).
-/

namespace H4320

open TM

/-! ## Bit lists -/

/-- The zone of the bits after a 1: each gap is a run starting with one bit and continuing with the 1s after it. -/
def zoneOf : List Bool → List Nat
  | [] => [3]
  | false :: bs => 3 :: zoneOf bs
  | true :: bs => ((zoneOf bs).headD 0 + 4) :: (zoneOf bs).tail

/-- The counter of a bit list (lowest bit first): the zeros below the lowest 1 in the last block, the rest in the
zone.  All bits 0 is the first moment of a round (`2^m` sub-rounds left). -/
def czb : List Bool → Nat × List Nat
  | [] => (1, [])
  | true :: bs => (1, zoneOf bs)
  | false :: bs => ((czb bs).1 + 4, (czb bs).2)

/-- One less, modulo `2^length`. -/
def bdec : List Bool → List Bool
  | [] => []
  | true :: bs => false :: bs
  | false :: bs => true :: bdec bs

def allF (bs : List Bool) : Bool := bs.all (· == false)

theorem zoneOf_ne : ∀ bs : List Bool, zoneOf bs ≠ []
  | [] => by simp [zoneOf]
  | false :: bs => by simp [zoneOf]
  | true :: bs => by simp [zoneOf]

theorem zoneOf_true (bs : List Bool) : ∃ g gs, zoneOf bs = g :: gs ∧ zoneOf (true :: bs) = (g + 4) :: gs := by
  cases e : zoneOf bs with
  | nil => exact absurd e (zoneOf_ne bs)
  | cons g gs => exact ⟨g, gs, rfl, by simp [zoneOf, e]⟩

theorem zoneOf_bdec : ∀ bs : List Bool, zoneOf (bdec bs) = ((czb bs).1 + 2) :: (czb bs).2
  | [] => rfl
  | true :: bs => rfl
  | false :: bs => by
    simp only [bdec, zoneOf, czb, zoneOf_bdec bs, List.headD, List.tail]

theorem gpop_zoneOf : ∀ (bs : List Bool) (n : Nat), allF bs = false →
    gpop (zoneOf bs) n = some ((czb bs).1 + 4 + 4 * n, (czb bs).2)
  | [], _, h => by simp [allF] at h
  | false :: bs, n, h => by
    simp only [allF, List.all_cons, beq_self_eq_true, Bool.true_and] at h
    simp only [zoneOf, gpop, czb]
    rw [gpop_zoneOf bs (n + 1) h]
    simp only [Option.some.injEq, Prod.mk.injEq, and_true]
    omega
  | true :: bs, n, _ => by
    obtain ⟨g, gs, e1, e2⟩ := zoneOf_true bs
    rw [e2]
    simp only [gpop, czb, e1, Option.some.injEq, Prod.mk.injEq, and_true]
    omega

theorem zoneOf_allF : ∀ bs : List Bool, allF bs = true → zoneOf bs = List.replicate (bs.length + 1) 3
  | [], _ => rfl
  | false :: bs, h => by
    simp only [allF, List.all_cons, beq_self_eq_true, Bool.true_and] at h
    simp only [zoneOf, zoneOf_allF bs h, List.length_cons, List.replicate_succ]
  | true :: bs, h => by simp [allF] at h

theorem czb_allF : ∀ bs : List Bool, allF bs = true → czb bs = (4 * bs.length + 1, [])
  | [], _ => rfl
  | false :: bs, h => by
    simp only [allF, List.all_cons, beq_self_eq_true, Bool.true_and] at h
    simp only [czb, czb_allF bs h, List.length_cons, Prod.mk.injEq, and_true]
    omega
  | true :: bs, h => by simp [allF] at h

theorem allF_replicate (n : Nat) : allF (List.replicate n false) = true := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, allF, List.all_cons, beq_self_eq_true, Bool.true_and]; exact ih

/-- The last sub-round of a round: the bits of 1 (or no bits). -/
def isOne : List Bool → Bool
  | [] => true
  | b :: bs => b && allF bs

/-- **The counter is a binary decrement.** -/
theorem gstep_czb_dec : ∀ bs : List Bool, isOne bs = false → gstep (czb bs) = some (czb (bdec bs))
  | [], h => by simp [isOne] at h
  | false :: bs, _ => by
    show gstep ((czb bs).1 + 2 + 2, (czb bs).2) = _
    simp only [gstep, bdec, czb, zoneOf_bdec]
  | true :: bs, h => by
    simp only [isOne, Bool.true_and] at h
    show gpop (zoneOf bs) 0 = _
    rw [gpop_zoneOf bs 0 h]
    rfl

/-- **The end of a round**: the next one starts with all bits 0, one bit more. -/
theorem gstep_czb_one : ∀ bs : List Bool, isOne bs = true →
    gstep (czb bs) = some (czb (List.replicate (bs.length + 1) false))
  | [], _ => rfl
  | false :: bs, h => by simp [isOne] at h
  | true :: bs, h => by
    simp only [isOne, Bool.true_and] at h
    show gpop (zoneOf bs) 0 = _
    rw [zoneOf_allF bs h, gpop_threes, czb_allF _ (allF_replicate _)]
    simp only [List.length_replicate, List.length_cons, Option.some.injEq, Prod.mk.injEq, and_true]
    omega

/-! ## Numbers -/

/-- The lowest `m` bits of `r`, lowest first. -/
def bits : Nat → Nat → List Bool
  | 0, _ => []
  | m + 1, r => (r % 2 == 1) :: bits m (r / 2)

def valB : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * valB bs

theorem mod_pow_succ' (x m : Nat) : x % 2 ^ (m + 1) = x % 2 + 2 * (x / 2 % 2 ^ m) := by
  rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul]

theorem bits_length : ∀ m r, (bits m r).length = m
  | 0, _ => rfl
  | m + 1, r => by simp [bits, bits_length m]

theorem bits_eq_of_mod : ∀ m x y, x % 2 ^ m = y % 2 ^ m → bits m x = bits m y
  | 0, _, _, _ => rfl
  | m + 1, x, y, h => by
    rw [mod_pow_succ', mod_pow_succ' y] at h
    have hx := Nat.mod_two_eq_zero_or_one x
    have hy := Nat.mod_two_eq_zero_or_one y
    have h1 : x % 2 = y % 2 := by omega
    have h2 : x / 2 % 2 ^ m = y / 2 % 2 ^ m := by omega
    simp only [bits, h1, bits_eq_of_mod m _ _ h2]

theorem bits_mod (m x : Nat) : bits m (x % 2 ^ m) = bits m x :=
  bits_eq_of_mod m _ _ (Nat.mod_mod _ _)

theorem bits_allF_iff : ∀ m r, allF (bits m r) = true ↔ r % 2 ^ m = 0
  | 0, r => by simp [bits, allF, Nat.mod_one]
  | m + 1, r => by
    have ih := bits_allF_iff m (r / 2)
    rw [mod_pow_succ']
    simp only [bits, allF, List.all_cons, Bool.and_eq_true, beq_iff_eq] at ih ⊢
    rw [ih]
    have hx := Nat.mod_two_eq_zero_or_one r
    constructor
    · rintro ⟨h1, h2⟩
      have : r % 2 = 0 := by cases hx with
        | inl h => exact h
        | inr h => simp [h] at h1
      omega
    · intro h
      refine ⟨?_, by omega⟩
      have : r % 2 = 0 := by omega
      simp [this]

theorem bdec_bits : ∀ m r, bdec (bits m r) = bits m (r + 2 ^ m - 1)
  | 0, _ => rfl
  | m + 1, r => by
    rcases Nat.mod_two_eq_zero_or_one r with h | h
    · have e1 : (r + 2 ^ (m + 1) - 1) % 2 = 1 := by have := Nat.two_pow_pos m; rw [Nat.pow_succ]; omega
      have e2 : (r + 2 ^ (m + 1) - 1) / 2 = r / 2 + 2 ^ m - 1 := by
        have := Nat.two_pow_pos m; rw [Nat.pow_succ]; omega
      simp only [bits, h, e1, e2, bdec, show ((0 : Nat) == 1) = false from rfl, beq_self_eq_true,
        bdec_bits m (r / 2)]
    · have e1 : (r + 2 ^ (m + 1) - 1) % 2 = 0 := by rw [Nat.pow_succ]; omega
      have e2 : (r + 2 ^ (m + 1) - 1) / 2 = r / 2 + 2 ^ m := by rw [Nat.pow_succ]; omega
      simp only [bits, h, e1, e2, bdec, show ((0 : Nat) == 1) = false from rfl, beq_self_eq_true]
      congr 1
      apply bits_eq_of_mod
      simp

/-- The counter in round `m` with `r` sub-rounds left (`1 ≤ r ≤ 2^m`). -/
def cz (m r : Nat) : Nat × List Nat := czb (bits m r)

/-- The counter after `A ≥ 1` steps from the start of round 0. -/
def cv (A : Nat) : Nat × List Nat := cz (Nat.log2 A) (2 ^ (Nat.log2 A + 1) - A)

theorem log2_of (A m : Nat) (h1 : 2 ^ m ≤ A) (h2 : A < 2 ^ (m + 1)) : Nat.log2 A = m := by
  have hA : A ≠ 0 := by have := Nat.two_pow_pos m; omega
  exact (Nat.log2_eq_iff hA).2 ⟨h1, h2⟩

theorem isOne_bits (m r : Nat) (hm : 1 ≤ m) : isOne (bits m r) = true ↔ r % 2 ^ m = 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  simp only [bits, isOne, Bool.and_eq_true, beq_iff_eq]
  rw [bits_allF_iff, mod_pow_succ']
  have hx := Nat.mod_two_eq_zero_or_one r
  omega

theorem bits_zero : ∀ m, bits m 0 = List.replicate m false
  | 0 => rfl
  | m + 1 => by simp [bits, bits_zero m, List.replicate_succ]

theorem gstep_cv (A : Nat) (hA : 1 ≤ A) : gstep (cv A) = some (cv (A + 1)) := by
  have hA0 : A ≠ 0 := by omega
  have h1 := Nat.log2_self_le hA0
  have h2 := @Nat.lt_log2_self A
  generalize hm : Nat.log2 A = m at h1 h2
  have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
  unfold cv cz
  rw [hm]
  by_cases hlast : A + 1 = 2 ^ (m + 1)
  · have hm' : Nat.log2 (A + 1) = m + 1 := log2_of _ _ (by omega) (by rw [Nat.pow_succ]; omega)
    rw [hm', show 2 ^ (m + 1) - A = 1 by omega]
    have hone : isOne (bits m 1) = true := by
      cases m with
      | zero => rfl
      | succ j => rw [isOne_bits _ _ (by omega)]; exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
    rw [gstep_czb_one _ hone, bits_length]
    have e : 2 ^ (m + 1 + 1) - (A + 1) = 2 ^ (m + 1) := by rw [hlast]; have := Nat.pow_succ 2 (m + 1); omega
    rw [e, ← bits_mod, Nat.mod_self, bits_zero]
  · have hm' : Nat.log2 (A + 1) = m := log2_of _ _ (by omega) (by omega)
    rw [hm']
    have hr : 2 ≤ 2 ^ (m + 1) - A := by omega
    have hnot : isOne (bits m (2 ^ (m + 1) - A)) = false := by
      cases m with
      | zero => omega
      | succ j =>
        cases e : isOne (bits (j + 1) (2 ^ (j + 1 + 1) - A)) with
        | false => rfl
        | true =>
          rw [isOne_bits _ _ (by omega)] at e
          exfalso
          by_cases hlt : 2 ^ (j + 1 + 1) - A < 2 ^ (j + 1)
          · rw [Nat.mod_eq_of_lt hlt] at e; omega
          · have : 2 ^ (j + 1 + 1) - A = 2 ^ (j + 1) := by omega
            rw [this, Nat.mod_self] at e; omega
    rw [gstep_czb_dec _ hnot, bdec_bits]
    congr 2
    apply bits_eq_of_mod
    rw [show 2 ^ (m + 1) - A + 2 ^ m - 1 = (2 ^ (m + 1) - (A + 1)) + 2 ^ m by omega, Nat.add_mod_right]

/-- **The counter in closed form.** -/
theorem giter_cv (N : Nat) : ∀ A, 1 ≤ A → giter N (cv A) = some (cv (A + N)) := by
  induction N with
  | zero => intro A _; rfl
  | succ N ih =>
    intro A hA
    simp only [giter, gstep_cv A hA, Option.bind_some]
    rw [ih (A + 1) (by omega), show A + 1 + N = A + (N + 1) by omega]

theorem cv_cz (A m : Nat) (h1 : 2 ^ m ≤ A) (h2 : A < 2 ^ (m + 1)) : cv A = cz m (2 ^ (m + 1) - A) := by
  unfold cv; rw [log2_of A m h1 h2]

/-- **The counter in closed form**, round by round: from round `m` with `r` sub-rounds left, `N` steps later the
counter is in the round `m'` of `V = 2^(m+1) - r + N` sub-rounds from the start. -/
theorem giter_cz (N m r m' : Nat) (h1 : 1 ≤ r) (h2 : r ≤ 2 ^ m) (h3 : 2 ^ m' ≤ 2 ^ (m + 1) - r + N)
    (h4 : 2 ^ (m + 1) - r + N < 2 ^ (m' + 1)) :
    giter N (cz m r) = some (cz m' (2 ^ (m' + 1) - (2 ^ (m + 1) - r + N))) := by
  have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
  have e : cz m r = cv (2 ^ (m + 1) - r) := by
    rw [cv_cz _ m (by omega) (by omega)]; congr 1; omega
  rw [e, giter_cv N _ (by have := Nat.two_pow_pos m; omega), cv_cz _ m' h3 h4]

/-! ## Cutting a counter at a 0 bit -/

theorem zoneOf_append : ∀ (L H : List Bool), zoneOf (L ++ false :: H) = zoneOf L ++ zoneOf H
  | [], H => rfl
  | false :: L, H => by simp only [List.cons_append, zoneOf, zoneOf_append L H, List.cons_append]
  | true :: L, H => by
    simp only [List.cons_append, zoneOf, zoneOf_append L H]
    obtain ⟨g, gs, e, _⟩ := zoneOf_true L
    rw [e]; rfl

theorem czb_append : ∀ (L H : List Bool), allF L = false →
    czb (L ++ false :: H) = ((czb L).1, (czb L).2 ++ zoneOf H)
  | [], _, h => by simp [allF] at h
  | true :: L, H, _ => by simp only [List.cons_append, czb, zoneOf_append]
  | false :: L, H, h => by
    simp only [allF, List.all_cons, beq_self_eq_true, Bool.true_and] at h
    simp only [List.cons_append, czb, czb_append L H h]

theorem bits_add : ∀ (p h r : Nat), bits (p + h) r = bits p r ++ bits h (r / 2 ^ p)
  | 0, h, r => by simp [bits]
  | p + 1, h, r => by
    rw [show p + 1 + h = (p + h) + 1 by omega]
    simp only [bits, bits_add p h (r / 2), List.cons_append, Nat.div_div_eq_div_mul, Nat.pow_succ]
    rw [Nat.mul_comm 2 (2 ^ p)]

/-- **The cut.**  A counter whose bit `p` is 0 is the gaps of the bits below `p`, then the gaps of the bits above. -/
theorem cz_split (m p r : Nat) (hp : p < m) (h0 : r / 2 ^ p % 2 = 0) (hl : r % 2 ^ p ≠ 0) :
    cz m r = ((czb (bits p r)).1, (czb (bits p r)).2 ++ zoneOf (bits (m - p - 1) (r / 2 ^ (p + 1)))) := by
  unfold cz
  have e : m = p + (1 + (m - p - 1)) := by omega
  rw [e, bits_add, bits_add (h := m - p - 1) 1]
  simp only [bits, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
  have hb : (r / 2 ^ p % 2 == 1) = false := by simp [h0]
  rw [hb, show p + (1 + (m - p - 1)) - p - 1 = m - p - 1 by omega]
  have hL : allF (bits p r) = false := by
    cases e2 : allF (bits p r) with
    | false => rfl
    | true => exact absurd ((bits_allF_iff p r).1 e2) hl
  rw [List.singleton_append, czb_append _ _ hL]

theorem valB_lt : ∀ L : List Bool, valB L < 2 ^ L.length
  | [] => by simp [valB]
  | b :: bs => by
    have := valB_lt bs
    simp only [valB, List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

theorem bits_valB : ∀ L : List Bool, bits L.length (valB L) = L
  | [] => rfl
  | b :: bs => by
    simp only [List.length_cons, bits, valB]
    cases b
    · simp only [Bool.false_eq_true, ite_false, Nat.zero_add]
      rw [show 2 * valB bs % 2 = 0 by omega, show 2 * valB bs / 2 = valB bs by omega, bits_valB bs]
      rfl
    · simp only [ite_true]
      rw [show (1 + 2 * valB bs) % 2 = 1 by omega, show (1 + 2 * valB bs) / 2 = valB bs by omega, bits_valB bs]
      rfl

/-- **The join.**  A low counter `czb L'` (not all bits 0) followed by the gaps of the bits above a 0 bit is the
counter with the bits of `L'`, a 0, and those bits. -/
theorem cz_join (L' : List Bool) (h H : Nat) (hL : allF L' = false) :
    ((czb L').1, (czb L').2 ++ zoneOf (bits h H)) = cz (L'.length + 1 + h) (valB L' + 2 ^ (L'.length + 1) * H) := by
  unfold cz
  rw [← czb_append _ _ hL]
  congr 1
  rw [show L'.length + 1 + h = L'.length + (h + 1) by omega, bits_add]
  have hv := valB_lt L'
  have e1 : valB L' + 2 ^ (L'.length + 1) * H = valB L' + 2 ^ L'.length * (2 * H) := by
    rw [Nat.pow_succ]; rw [Nat.mul_assoc, Nat.mul_comm 2 H]
  rw [e1]
  have e2 : bits L'.length (valB L' + 2 ^ L'.length * (2 * H)) = L' := by
    rw [bits_eq_of_mod _ _ (valB L') (by simp [Nat.add_mul_mod_self_left]), bits_valB]
  have e3 : (valB L' + 2 ^ L'.length * (2 * H)) / 2 ^ L'.length = 2 * H := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hv, Nat.zero_add]
  rw [e2, e3]
  simp only [bits, show 2 * H % 2 = 0 by omega, show 2 * H / 2 = H by omega]
  rfl

end H4320
