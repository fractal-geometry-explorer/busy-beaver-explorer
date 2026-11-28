import Ones

/-!
# 1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE: the phase map at its stops is the doubling map

At the left and right stops `E(x, z)` (`z` even) and `A(x, y)` (`y` even) put `s = z + 2`, `L = 2x + z + 8` and
`s = y + 6`, `L = 2x + y + 8` (`sv`).  Then the next stop, one to three phases on, has modulus `L + 2` and
`s' = 2s` if `2s ≤ L`, `s' = 2s - L` otherwise (`doubling`): the run is the doubling map `s ↦ 2s mod L` with a
modulus that grows by 2 a stop.  It fails only at `s = 4` (`E(x, 2)`, `low`: `s' = 16 = 4s`), at the safe all-ones
tapes `A(0, y)` of even length (`ones_even`: one extra step, modulus `L + 4`), and at `2s = L + 2`, where the next stop
is the all-ones tape of odd length `L - 5` (`mid_ones`).  Fatal lengths (`Fatal`) are 3 and `28·2^k - 2k - 13`, all
odd.
-/

namespace H35167

theorem iter_step {p q : Ph} (j : Nat) (h : next p = some q) : iter (j + 1) p = iter j q := by
  simp [iter, h]

theorem n_e (x z : Nat) (h : 2 ≤ z) : next (.e x z) = some (.q x 0 (z - 2)) := by
  obtain ⟨u, rfl⟩ : ∃ u, z = u + 2 := ⟨z - 2, by omega⟩; simp [next]
theorem n_q5 (k t : Nat) (h : 5 ≤ t) : next (.q 0 k t) = some (.e (2 * k + 4) (t - 4)) := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 5 := ⟨t - 5, by omega⟩; simp [next]
theorem n_q4 (k : Nat) : next (.q 0 k 4) = some (.a 0 (4 * k + 9)) := by simp [next]
theorem n_q2 (m k : Nat) : next (.q m k 2) = some (.a m (4 * k + 6)) := by simp [next]
theorem n_qall (m k t : Nat) (h1 : 1 ≤ m) (h2 : 2 * m + 1 ≤ t) :
    next (.q m k t) = some (.q 0 (k + m) (t - 2 * m)) := by
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 3 := ⟨t - 3, by omega⟩
  simp only [next, Nat.min_eq_left (show a + 1 ≤ (u + 2) / 2 by omega), Nat.sub_self]
theorem n_qeven (m k b : Nat) (h1 : 1 ≤ b) (h2 : b ≤ m) :
    next (.q m k (2 * b + 2)) = some (.q (m - b) (k + b) 2) := by
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
  obtain ⟨u, rfl⟩ : ∃ u, b = u + 1 := ⟨b - 1, by omega⟩
  rw [show 2 * (u + 1) + 2 = (2 * u + 1) + 3 by omega]
  simp only [next, Nat.min_eq_right (show (2 * u + 1 + 2) / 2 ≤ a + 1 by omega), Option.some.injEq, Ph.q.injEq]
  omega
theorem n_a (X y : Nat) : next (.a (X + 2) y) = some (.q X 0 (y + 2)) := by simp [next]
theorem n_a1 (y : Nat) (h : 1 ≤ y) : next (.a 1 y) = some (.e 2 y) := by
  obtain ⟨u, rfl⟩ : ∃ u, y = u + 1 := ⟨y - 1, by omega⟩; simp [next]

/-- The doubling coordinates of a left or right stop: `s` and the modulus `L`. -/
def sv : Ph → Nat × Nat
  | .e x z => (z + 2, 2 * x + z + 8)
  | .a x y => (y + 6, 2 * x + y + 8)
  | .q _ _ _ => (0, 0)

/-- `p'` is the doubling-map image of `p`: the modulus grows by 2 and `s' = 2s mod L`. -/
def Dbl (p p' : Ph) : Prop :=
  (sv p').2 = (sv p).2 + 2 ∧
    ((2 * (sv p).1 ≤ (sv p).2 ∧ (sv p').1 = 2 * (sv p).1) ∨
     ((sv p).2 < 2 * (sv p).1 ∧ (sv p').1 + (sv p).2 = 2 * (sv p).1))

/-- The stops of the doubling map: `E(x, z)` with `z` even, `z ≥ 2`, and `A(x, y)` with `y` even (an even phase, or for
`x = 0` an all-ones tape of even length). -/
def Good (p : Ph) : Prop := (∃ x z, p = .e x z ∧ z % 2 = 0 ∧ 2 ≤ z) ∨ (∃ x y, p = .a x y ∧ y % 2 = 0)

theorem ex_e (x z : Nat) (he : z % 2 = 0) (h4 : 4 ≤ z) (hm : z ≠ 2 * x + 6) :
    ∃ j p', 1 ≤ j ∧ j ≤ 3 ∧ iter j (.e x z) = some p' ∧ Good p' ∧ Dbl (.e x z) p' := by
  obtain ⟨c, rfl⟩ : ∃ c, z = 2 * c + 2 := ⟨(z - 2) / 2, by omega⟩
  rcases Nat.lt_or_ge c 2 with hc | hc
  · obtain rfl : c = 1 := by omega
    refine ⟨2, _, by omega, by omega,
      (by rw [iter_step 1 (n_e x _ (by omega)), iter_step 0 (n_q2 x 0)]; rfl), ?_, ?_⟩
    · exact Or.inr ⟨_, _, rfl, by omega⟩
    · simp [Dbl, sv] <;> omega
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · have : 3 ≤ c := by omega
    refine ⟨2, _, by omega, by omega,
      (by rw [iter_step 1 (n_e 0 _ (by omega)), iter_step 0 (n_q5 0 _ (by omega))]; rfl), ?_, ?_⟩
    · exact Or.inl ⟨_, _, rfl, by omega, by omega⟩
    · simp [Dbl, sv] <;> omega
  rcases Nat.lt_or_ge x (c - 1) with hb | hb
  · have : x + 3 ≤ c := by omega
    refine ⟨3, _, by omega, by omega,
      (by rw [iter_step 2 (n_e x _ (by omega)), iter_step 1 (n_qall x 0 _ (by omega) (by omega)),
              iter_step 0 (n_q5 _ _ (by omega))]; rfl), ?_, ?_⟩
    · exact Or.inl ⟨_, _, rfl, by omega, by omega⟩
    · simp [Dbl, sv] <;> omega
  · refine ⟨3, _, by omega, by omega,
      (by rw [iter_step 2 (n_e x _ (by omega)),
              show 2 * c + 2 - 2 = 2 * (c - 1) + 2 by omega,
              iter_step 1 (n_qeven x 0 (c - 1) (by omega) (by omega)), iter_step 0 (n_q2 _ _)]; rfl), ?_, ?_⟩
    · exact Or.inr ⟨_, _, rfl, by omega⟩
    · simp [Dbl, sv] <;> omega

theorem ex_a (x y : Nat) (hx : 1 ≤ x) (hy : y % 2 = 0) (hm : y + 2 ≠ 2 * x) :
    ∃ j p', 1 ≤ j ∧ j ≤ 3 ∧ iter j (.a x y) = some p' ∧ Good p' ∧ Dbl (.a x y) p' := by
  obtain ⟨d, rfl⟩ : ∃ d, y = 2 * d := ⟨y / 2, by omega⟩
  rcases Nat.lt_or_ge x 2 with hx2 | hx2
  · obtain rfl : x = 1 := by omega
    refine ⟨1, _, by omega, by omega, (by rw [iter_step 0 (n_a1 _ (by omega))]; rfl), ?_, ?_⟩
    · exact Or.inl ⟨_, _, rfl, by omega, by omega⟩
    · simp [Dbl, sv] <;> omega
  obtain ⟨X, rfl⟩ : ∃ X, x = X + 2 := ⟨x - 2, by omega⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨2, _, by omega, by omega,
      (by rw [iter_step 1 (n_a X _), iter_step 0 (n_q2 _ _)]; rfl), ?_, ?_⟩
    · exact Or.inr ⟨_, _, rfl, by omega⟩
    · simp [Dbl, sv] <;> omega
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · have : 2 ≤ d := by omega
    refine ⟨2, _, by omega, by omega,
      (by rw [iter_step 1 (n_a 0 _), iter_step 0 (n_q5 _ _ (by omega))]; rfl), ?_, ?_⟩
    · exact Or.inl ⟨_, _, rfl, by omega, by omega⟩
    · simp [Dbl, sv] <;> omega
  rcases Nat.lt_or_ge X d with hb | hb
  · have : X + 2 ≤ d := by omega
    refine ⟨3, _, by omega, by omega,
      (by rw [iter_step 2 (n_a X _), iter_step 1 (n_qall X 0 _ (by omega) (by omega)),
              iter_step 0 (n_q5 _ _ (by omega))]; rfl), ?_, ?_⟩
    · exact Or.inl ⟨_, _, rfl, by omega, by omega⟩
    · simp [Dbl, sv] <;> omega
  · refine ⟨3, _, by omega, by omega,
      (by rw [iter_step 2 (n_a X _), iter_step 1 (n_qeven X 0 d (by omega) (by omega)), iter_step 0 (n_q2 _ _)];
          rfl), ?_, ?_⟩
    · exact Or.inr ⟨_, _, rfl, by omega⟩
    · simp [Dbl, sv] <;> omega

/-- **The doubling map.**  From a stop `p` (`Good`, not an all-ones tape) with `s ≠ 4` and `2s ≠ L + 2`, the next
stop `p'`, one to three phases on, is again a stop, with modulus `L + 2` and `s' = 2s mod L`. -/
theorem doubling (p : Ph) (hg : Good p) (h0 : ∀ y, p ≠ .a 0 y) (h4 : (sv p).1 ≠ 4)
    (hm : 2 * (sv p).1 ≠ (sv p).2 + 2) :
    ∃ j p', 1 ≤ j ∧ j ≤ 3 ∧ iter j p = some p' ∧ Good p' ∧ Dbl p p' := by
  rcases hg with ⟨x, z, rfl, hz, hz2⟩ | ⟨x, y, rfl, hy⟩
  · simp only [sv] at h4 hm
    exact ex_e x z hz (by omega) (by omega)
  · simp only [sv] at h4 hm
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · exact absurd rfl (h0 y)
    · exact ex_a x y hx hy (by omega)

/-- **The only all-ones tapes of odd length.**  At a stop with `2s = L + 2` the next stop is the all-ones tape of
odd length `L - 5`. -/
theorem mid_ones (p : Ph) (hg : Good p) (hm : 2 * (sv p).1 = (sv p).2 + 2) :
    ∃ j, 1 ≤ j ∧ j ≤ 3 ∧ iter j p = some (.a 0 ((sv p).2 - 5)) ∧ ((sv p).2 - 5) % 2 = 1 := by
  rcases hg with ⟨x, z, rfl, hz, hz2⟩ | ⟨x, y, rfl, hy⟩
  · simp only [sv] at hm ⊢
    obtain rfl : z = 2 * x + 6 := by omega
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · refine ⟨2, by omega, by omega, ?_, by omega⟩
      rw [iter_step 1 (n_e 0 _ (by omega)), iter_step 0 (n_q4 _)]; rfl
    · refine ⟨3, by omega, by omega, ?_, by omega⟩
      rw [iter_step 2 (n_e x (2 * x + 6) (by omega)), iter_step 1 (n_qall x 0 (2 * x + 6 - 2) hx (by omega)),
          show 2 * x + 6 - 2 - 2 * x = 4 by omega, iter_step 0 (n_q4 _)]
      simp only [iter, Option.some.injEq, Ph.a.injEq, true_and]; omega
  · simp only [sv] at hm ⊢
    obtain rfl : y = 2 * x - 2 := by omega
    rcases Nat.lt_or_ge x 2 with hx | hx
    · rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl
      · simp at hm
      · exact ⟨1, by omega, by omega, by simp [iter, next], by omega⟩
    obtain ⟨X, rfl⟩ : ∃ X, x = X + 2 := ⟨x - 2, by omega⟩
    rcases Nat.eq_zero_or_pos X with rfl | hX
    · exact ⟨2, by omega, by omega, by simp [iter, next], by omega⟩
    · refine ⟨3, by omega, by omega, ?_, by omega⟩
      rw [iter_step 2 (n_a X (2 * (X + 2) - 2)), iter_step 1 (n_qall X 0 (2 * (X + 2) - 2 + 2) hX (by omega)),
          show 2 * (X + 2) - 2 + 2 - 2 * X = 4 by omega, iter_step 0 (n_q4 _)]
      simp only [iter, Option.some.injEq, Ph.a.injEq, true_and]; omega

/-- **The safe all-ones tapes.**  `A(0, y)` with `y ≥ 4` even goes to `E(3, y - 2)`: `s' = 2s - L - 4`, modulus
`L + 4`. -/
theorem ones_even (y : Nat) (h : 4 ≤ y) : iter 1 (.a 0 y) = some (.e 3 (y - 2)) := by
  obtain ⟨u, rfl⟩ : ∃ u, y = u + 3 := ⟨y - 3, by omega⟩; simp [iter, next]

/-- **The low exception.**  At `s = 4` (`E(x, 2)`, `x ≥ 3`) the next stop is `A(x - 3, 10)`: modulus `L + 2` again,
but `s' = 16 = 4s`. -/
theorem low (x : Nat) : iter 4 (.e (x + 3) 2) = some (.a x 10) := by simp [iter, next]

end H35167
