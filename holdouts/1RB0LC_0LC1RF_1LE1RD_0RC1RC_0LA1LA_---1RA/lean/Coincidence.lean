import HaltIff

/-!
# Halting is a Euclid coincidence, and no residue argument can rule it out

`halts_iff` (in `HaltIff.lean`) says the machine halts exactly when the orbit of `next` from `U(4, 3)` reaches an
event with `a ≡ 0 (mod 4)` and `b = 1`.  This file sharpens it twice.

* `halts_iff_b1`: the condition `a ≡ 0 (mod 4)` can be dropped.  At `b = 1` with `a ≡ 2 (mod 4)` the map keeps
  `b = 1` and sends `a` to `(3a + 10)/2`, so `a + 10` is multiplied by 3/2; it loses a factor 2 each time, and
  once `a + 10 ≡ 2 (mod 4)` we have `a ≡ 0 (mod 4)` and the machine halts.
* `halts_iff_coincidence`: the machine halts exactly when the orbit meets an event with both numbers even and
  `b = a + 4` or `b = a − 2`.  Every rule that makes `b = 1` either starts from `b = 1` or is a Euclid step from
  such an event (`next_to_b1`), and conversely every such event goes to `b = 1` (`next_of_coincidence`).

`no_residue_proof`: for every modulus `1 ≤ M ≤ 10000`, no property of the residues `(kind, a mod M, b mod M)`
that holds along the orbit can exclude these coincidence events: the orbit itself visits, within its first 10⁵
passes, an event whose residues are those of a coincidence event.  So a non-halting proof cannot be a congruence
argument modulo any such M (`sweep`, checked with `native_decide`).
-/

namespace H13743

open TM

/-- Like `ite_cases`, but the branch not taken forgets its negated condition (keeps `omega` fast). -/
theorem ite_cases' {α : Type} {c : Prop} [Decidable c] {v : α} {e : Option α} {r : α}
    (h : (if c then some v else e) = some r) : (c ∧ v = r) ∨ e = some r := by
  rcases ite_cases h with h | h
  · exact Or.inl h
  · exact Or.inr h.2

theorem nextU_to_b1 (a b : Nat) (r : Tag × Nat × Nat × Nat) (hi : Inv a b) (h : nextU a b = some r)
    (h1 : r.2.2.1 = 1) : (b = 1 ∧ a % 4 = 2) ∨ (b % 2 = 0 ∧ (b = a + 4 ∨ a = b + 2)) := by
  unfold Inv at hi
  unfold nextU at h
  repeat' (obtain ⟨_, rfl⟩ | h := ite_cases' h)
  all_goals first | (dsimp only at h1; omega) | cases h

theorem nextV_to_b1 (a b : Nat) (r : Tag × Nat × Nat × Nat) (hi : Inv a b) (h : nextV a b = some r)
    (h1 : r.2.2.1 = 1) : (b = 1 ∧ a % 4 = 2) ∨ (b % 2 = 0 ∧ (b = a + 4 ∨ a = b + 2)) := by
  unfold Inv at hi
  unfold nextV at h
  repeat' (obtain ⟨_, rfl⟩ | h := ite_cases' h)
  all_goals first | (dsimp only at h1; omega) | cases h

/-- **Where b = 1 comes from**: a pass ending at `b = 1` starts at `b = 1` (with `a ≡ 2 mod 4`) or at a
coincidence event (both even, `b = a + 4` or `b = a − 2`). -/
theorem next_to_b1 (F : Tag) (a b : Nat) (r : Tag × Nat × Nat × Nat) (hi : Inv a b) (h : next F a b = some r)
    (h1 : r.2.2.1 = 1) : (b = 1 ∧ a % 4 = 2) ∨ (b % 2 = 0 ∧ (b = a + 4 ∨ a = b + 2)) := by
  cases F with
  | U => exact nextU_to_b1 a b r hi h h1
  | V => exact nextV_to_b1 a b r hi h h1

theorem nextU_coinc (a b : Nat) (r : Tag × Nat × Nat × Nat) (hi : Inv a b) (h : nextU a b = some r)
    (hc : b % 2 = 0 ∧ (b = a + 4 ∨ a = b + 2)) : r.2.2.1 = 1 := by
  unfold Inv at hi
  unfold nextU at h
  repeat' (obtain ⟨_, rfl⟩ | h := ite_cases' h)
  all_goals first | (dsimp only; omega) | cases h

theorem nextV_coinc (a b : Nat) (r : Tag × Nat × Nat × Nat) (hi : Inv a b) (h : nextV a b = some r)
    (hc : b % 2 = 0 ∧ (b = a + 4 ∨ a = b + 2)) : r.2.2.1 = 1 := by
  unfold Inv at hi
  unfold nextV at h
  repeat' (obtain ⟨_, rfl⟩ | h := ite_cases' h)
  all_goals first | (dsimp only; omega) | cases h

/-- A coincidence event goes to `b = 1`. -/
theorem next_of_coincidence (F : Tag) (a b : Nat) (r : Tag × Nat × Nat × Nat) (hi : Inv a b)
    (h : next F a b = some r) (hc : b % 2 = 0 ∧ (b = a + 4 ∨ a = b + 2)) : r.2.2.1 = 1 := by
  cases F with
  | U => exact nextU_coinc a b r hi h hc
  | V => exact nextV_coinc a b r hi h hc

theorem nextU_b1 (a : Nat) (r : Tag × Nat × Nat × Nat) (hi : Inv a 1) (h : nextU a 1 = some r)
    (h2 : a % 4 = 2) : r.2.2.1 = 1 ∧ 2 * (r.2.1 + 10) = 3 * (a + 10) := by
  unfold Inv at hi
  unfold nextU at h
  repeat' (obtain ⟨_, rfl⟩ | h := ite_cases' h)
  all_goals first | (dsimp only; omega) | cases h

theorem nextV_b1 (a : Nat) (r : Tag × Nat × Nat × Nat) (hi : Inv a 1) (h : nextV a 1 = some r)
    (h2 : a % 4 = 2) : r.2.2.1 = 1 ∧ 2 * (r.2.1 + 10) = 3 * (a + 10) := by
  unfold Inv at hi
  unfold nextV at h
  repeat' (obtain ⟨_, rfl⟩ | h := ite_cases' h)
  all_goals first | (dsimp only; omega) | cases h

/-- At `b = 1` with `a ≡ 2 (mod 4)` the map keeps `b = 1` and multiplies `a + 10` by 3/2. -/
theorem next_b1 (F : Tag) (a : Nat) (r : Tag × Nat × Nat × Nat) (hi : Inv a 1) (h : next F a 1 = some r)
    (h2 : a % 4 = 2) : r.2.2.1 = 1 ∧ 2 * (r.2.1 + 10) = 3 * (a + 10) := by
  cases F with
  | U => exact nextU_b1 a r hi h h2
  | V => exact nextV_b1 a r hi h h2

/-- Every positive number is a power of 2 times an odd number. -/
theorem two_adic : ∀ n x, 0 < x → x ≤ n → ∃ j m, x = 2 ^ j * m ∧ m % 2 = 1 := by
  intro n
  induction n with
  | zero => intro x h0 h; omega
  | succ n ih =>
    intro x h0 hx
    by_cases hp : x % 2 = 1
    · exact ⟨0, x, by simp, hp⟩
    · obtain ⟨j, m, e, hm⟩ := ih (x / 2) (by omega) (by omega)
      refine ⟨j + 1, m, ?_, hm⟩
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_assoc, ← e]
      omega

theorem orbit_none_succ : ∀ k F a b, orbit k F a b = none → orbit (k + 1) F a b = none := by
  intro k
  induction k with
  | zero => intro F a b h; cases h
  | succ k ih =>
    intro F a b h
    unfold orbit at h ⊢
    cases e : next F a b with
    | none => rfl
    | some q =>
      obtain ⟨F₁, a₁, b₁, s⟩ := q
      rw [e] at h
      dsimp only at h ⊢
      cases e2 : orbit k F₁ a₁ b₁ with
      | none => rw [ih F₁ a₁ b₁ e2]; rfl
      | some p => rw [e2] at h; cases h

/-- An orbit event with `b = 1` leads to a halt. -/
theorem halts_of_b1 : ∀ j k F a t m, orbit k .U 4 3 = some (F, a, 1, t) → a + 10 = 2 ^ j * m → m % 2 = 1 →
    HaltsFromBlank := by
  have hi0 : Inv 4 3 := by unfold Inv; omega
  intro j
  induction j with
  | zero =>
    intro k F a t m e hx hm
    have hi := orbit_inv k .U 4 3 F a 1 t hi0 e
    unfold Inv at hi; simp at hx; omega
  | succ j ih =>
    intro k F a t m e hx hm
    have hi := orbit_inv k .U 4 3 F a 1 t hi0 e
    by_cases h4 : a % 4 = 0
    · exact halts_iff.2 ⟨k, F, a, 1, t, e, h4, rfl⟩
    · have h2 : a % 4 = 2 := by unfold Inv at hi; omega
      have hs := next_isSome F a 1 hi.1 hi.2.1 hi.2.2 (by omega)
      cases e2 : next F a 1 with
      | none => rw [e2] at hs; cases hs
      | some r =>
        obtain ⟨F₁, a₁, b₁, s⟩ := r
        obtain ⟨hb, ha⟩ := next_b1 F a _ hi e2 h2
        dsimp only at hb ha
        subst hb
        have e3 : orbit (k + 1) .U 4 3 = some (F₁, a₁, 1, t + s) := by
          rw [orbit_succ k .U 4 3 F a 1 t e, e2]; rfl
        -- a + 10 = 2^(j+1) m with m odd and a + 10 ≡ 0 (mod 4), so a₁ + 10 = 2^j (3m)
        cases j with
        | zero => simp at hx; omega
        | succ j =>
          apply ih k.succ F₁ a₁ (t + s) (3 * m) e3 _ (by omega)
          have : a + 10 = 2 * (2 ^ (j + 1) * m) := by
            rw [hx, Nat.pow_succ 2 (j + 1), Nat.mul_comm (2 ^ (j + 1)) 2, Nat.mul_assoc]
          rw [Nat.mul_left_comm]
          omega

/-- **Halts iff b = 1**: the machine halts from blank tape exactly when the orbit of `next` from `U(4, 3)` reaches
an event with `b = 1` (whatever `a mod 4` is). -/
theorem halts_iff_b1 : HaltsFromBlank ↔ ∃ k F a t, orbit k .U 4 3 = some (F, a, 1, t) := by
  have hi0 : Inv 4 3 := by unfold Inv; omega
  constructor
  · rintro hh
    obtain ⟨k, F, a, b, t, e, _, rfl⟩ := halts_iff.1 hh
    exact ⟨k, F, a, t, e⟩
  · rintro ⟨k, F, a, t, e⟩
    have hi := orbit_inv k .U 4 3 F a 1 t hi0 e
    obtain ⟨j, m, hx, hm⟩ := two_adic (a + 10) (a + 10) (by omega) (Nat.le_refl _)
    exact halts_of_b1 j k F a t m e hx hm

/-- A coincidence event: both numbers even, and `b = a + 4` or `b = a − 2`. -/
def Coinc (a b : Nat) : Prop := b % 2 = 0 ∧ (b = a + 4 ∨ a = b + 2)

/-- **Halts iff a Euclid coincidence.** The machine halts from blank tape exactly when the orbit of `next` from
`U(4, 3)` meets an event with both numbers even and `b − a ∈ {4, −2}`. -/
theorem halts_iff_coincidence :
    HaltsFromBlank ↔ ∃ k F a b t, orbit k .U 4 3 = some (F, a, b, t) ∧ Coinc a b := by
  have hi0 : Inv 4 3 := by unfold Inv; omega
  rw [halts_iff_b1]
  constructor
  · rintro ⟨k, hk⟩
    induction k with
    | zero => obtain ⟨F, a, t, e⟩ := hk; simp [orbit] at e
    | succ k ih =>
      obtain ⟨F₁, a₁, t₁, e1⟩ := hk
      cases e : orbit k .U 4 3 with
      | none => rw [orbit_none_succ k .U 4 3 e] at e1; cases e1
      | some p =>
        obtain ⟨F, a, b, t⟩ := p
        have hi := orbit_inv k .U 4 3 F a b t hi0 e
        rw [orbit_succ k .U 4 3 F a b t e] at e1
        cases e2 : next F a b with
        | none => rw [e2] at e1; cases e1
        | some r =>
          rw [e2] at e1
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e1
          rcases next_to_b1 F a b r hi e2 e1.2.2.1 with ⟨rfl, _⟩ | hc
          · exact ih ⟨F, a, t, e⟩
          · exact ⟨k, F, a, b, t, e, hc⟩
  · rintro ⟨k, F, a, b, t, e, hc⟩
    have hi := orbit_inv k .U 4 3 F a b t hi0 e
    have hs := next_isSome F a b hi.1 hi.2.1 hi.2.2 (by unfold Coinc at hc; omega)
    cases e2 : next F a b with
    | none => rw [e2] at hs; cases hs
    | some r =>
      obtain ⟨F₁, a₁, b₁, s⟩ := r
      have hb := next_of_coincidence F a b _ hi e2 hc
      dsimp only at hb
      subst hb
      refine ⟨k + 1, F₁, a₁, t + s, ?_⟩
      rw [orbit_succ k .U 4 3 F a b t e, e2]; rfl

/-! ## No congruence argument -/

/-- The residues of `(a, b)` modulo `M` are those of a coincidence event. -/
def coincRes (M a b : Nat) : Bool :=
  b % 2 == 0 && ((a + 4) % M == b % M || (b + 2) % M == a % M)

/-- Walk `n` passes of the orbit and drop from `rem` every modulus `M` at which some event has the residues of
a coincidence event. -/
def sweep : Nat → Tag → Nat → Nat → List Nat → List Nat
  | 0, _, a, b, rem => rem.filter (fun M => !coincRes M a b)
  | n + 1, F, a, b, rem =>
    let rem' := rem.filter (fun M => !coincRes M a b)
    match next F a b with
    | some (F', a', b', _) => sweep n F' a' b' rem'
    | none => rem'

theorem sweep_spec : ∀ n F a b rem M, M ∈ rem → M ∉ sweep n F a b rem →
    ∃ k F' a' b' t, orbit k F a b = some (F', a', b', t) ∧ coincRes M a' b' = true := by
  intro n
  induction n with
  | zero =>
    intro F a b rem M hm hn
    refine ⟨0, F, a, b, 0, rfl, ?_⟩
    unfold sweep at hn
    apply Classical.byContradiction
    intro hc
    exact hn (List.mem_filter.2 ⟨hm, by simpa using hc⟩)
  | succ n ih =>
    intro F a b rem M hm hn
    by_cases hc : coincRes M a b = true
    · exact ⟨0, F, a, b, 0, rfl, hc⟩
    · have hm' : M ∈ rem.filter (fun M => !coincRes M a b) := List.mem_filter.2 ⟨hm, by simpa using hc⟩
      unfold sweep at hn
      cases e : next F a b with
      | none => rw [e] at hn; exact absurd hm' hn
      | some q =>
        obtain ⟨F₁, a₁, b₁, s⟩ := q
        rw [e] at hn
        obtain ⟨k, F', a', b', t, e2, hc2⟩ := ih F₁ a₁ b₁ _ M hm' hn
        refine ⟨k + 1, F', a', b', s + t, ?_, hc2⟩
        unfold orbit; rw [e]; dsimp only; rw [e2]; rfl

/-- Every modulus `1 ≤ M ≤ 10000` is met within the first 10⁵ passes. -/
theorem sweep_100k : sweep 100000 .U 4 3 (List.range' 1 10000) = [] := by native_decide

/-- **No congruence proof.** For `1 ≤ M ≤ 10000`, any property `S` of `(kind, a mod M, b mod M)` that holds at
every event of the orbit also holds at some coincidence event (a valid event, `Inv`), which then reaches `b = 1`
and halts (`next_of_coincidence`, `halts_of_b1`).  So no such `S` can prove that the machine never halts. -/
theorem no_residue_proof (M : Nat) (h1 : 1 ≤ M) (h2 : M ≤ 10000) (S : Tag → Nat → Nat → Prop)
    (hS : ∀ k F a b t, orbit k .U 4 3 = some (F, a, b, t) → S F (a % M) (b % M)) :
    ∃ F a b, S F (a % M) (b % M) ∧ Inv a b ∧ Coinc a b := by
  have hi0 : Inv 4 3 := by unfold Inv; omega
  have hm : M ∈ List.range' 1 10000 := List.mem_range'_1.2 ⟨h1, by omega⟩
  have hn : M ∉ sweep 100000 .U 4 3 (List.range' 1 10000) := by rw [sweep_100k]; simp
  obtain ⟨k, F, a, b, t, e, hc⟩ := sweep_spec _ _ _ _ _ M hm hn
  have hi := orbit_inv k .U 4 3 F a b t hi0 e
  have hs := hS k F a b t e
  unfold coincRes at hc
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hc
  obtain ⟨hb, hc | hc⟩ := hc
  · refine ⟨F, a, a + 4, ?_, ?_, ?_⟩
    · rw [hc]; exact hs
    · unfold Inv at *; omega
    · unfold Coinc Inv at *; omega
  · refine ⟨F, b + 2, b, ?_, ?_, ?_⟩
    · rw [hc]; exact hs
    · unfold Inv at *; omega
    · unfold Coinc; omega

end H13743
