import Outer

/-!
# 1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE: halting is a question about the outer configurations

`outer_halts` (Outer.lean) shows that `O N = 1^N F>0 0 1^3` halts when `N = 2^(n+4) - 2n - 10`.  Here is the
converse: **the machine halts from blank tape if and only if its run passes an outer configuration `O N` with
`N = 2^(n+4) - 2n - 10`** (`halts_iff_outer`).

The argument is a parity invariant on the block machine.  The only halt is `X = 4` with nothing but units on the
right (`mstep_halt_iff`).  Between two outer configurations the left block `X` is

* *even* only during the first passes of an epoch (from an even `N`): rounds against the tail and merges, which take
  `X` down by 2 and 4.  `BadT X a r` (tail `2r + 3`) and `BadU X a` (only units) say that these passes end with
  exactly four 1s on the left; they are computed from `T` and are kept, in both directions, by every step;
* *odd or 0* from the first time it leaves that pattern (a left block of 2 becomes 5, odd blocks lose 2 or 4, a
  block of 1 is walked over and leaves 0, restarts give `2k + 7`) until the next outer configuration, and then it
  cannot be 4.

So within an epoch the run halts only if `BadT N 0 0`, which is `N = 2^(n+4) - 2n - 10`.  Everything is checked by
Lean's kernel.
-/

namespace H15252

open TM

/-- `O N`: the outer configuration `1^N F>0 0 1^3`. -/
def O (N : Nat) : Q := ⟨N, 0, .none, 0, some 0⟩

/-- From `⟨Y, 0, none, 0, some q⟩` the passes end with four 1s on the left. -/
def Hq (Y q : Nat) : Prop := ∃ n, Y = T n q

/-- From `⟨X, a, none, 0, some r⟩` (tail `2r + 3`) the passes end with four 1s on the left. -/
def BadT (X a r : Nat) : Prop := X = 2 * r + 6 ∨ (2 * r + 7 ≤ X ∧ Hq (X - 2 * r - 6) (a + 2 * r + 4))

/-- From `⟨X, a, none, 0, none⟩` (only units) the passes end with four 1s on the left. -/
def BadU (X a : Nat) : Prop := X = 4 ∨ (5 ≤ X ∧ Hq (X - 4) (a + 1))

theorem T_ge : ∀ n q, 2 * q + 6 ≤ T n q
  | 0, q => by simp [T]
  | n + 1, q => by simp only [T]; omega

theorem hq_unfold (Y q : Nat) : Hq Y q ↔ Y = 2 * q + 6 ∨ (2 * q + 7 ≤ Y ∧ Hq (Y - 2 * q - 6) (2 * q + 4)) := by
  constructor
  · rintro ⟨n, rfl⟩
    cases n with
    | zero => left; rfl
    | succ n =>
      right
      have := T_ge n (2 * q + 4)
      refine ⟨by simp only [T]; omega, n, ?_⟩
      simp only [T]; omega
  · rintro (h | ⟨h1, n, h2⟩)
    · exact ⟨0, h⟩
    · exact ⟨n + 1, by simp only [T]; omega⟩

theorem badT_succ (X a r : Nat) (hX : 3 ≤ X) : BadT (X - 2) (a + 2) r ↔ BadT X a (r + 1) := by
  unfold BadT
  rw [show X - 2 - 2 * r - 6 = X - 2 * (r + 1) - 6 by omega, show a + 2 + 2 * r + 4 = a + 2 * (r + 1) + 4 by omega]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · left; omega
    · right; exact ⟨by omega, h2⟩
  · rintro (h | ⟨h1, h2⟩)
    · left; omega
    · right; exact ⟨by omega, h2⟩

theorem badT_zero (X a : Nat) (hX : 3 ≤ X) : BadU (X - 2) (a + 3) ↔ BadT X a 0 := by
  unfold BadU BadT
  rw [show X - 2 - 4 = X - 2 * 0 - 6 by omega, show a + 3 + 1 = a + 2 * 0 + 4 by omega]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · left; omega
    · right; exact ⟨by omega, h2⟩
  · rintro (h | ⟨h1, h2⟩)
    · left; omega
    · right; exact ⟨by omega, h2⟩

theorem badU_merge (X a : Nat) (hX : 5 ≤ X) : BadT (X - 4) 0 (a + 1) ↔ BadU X a := by
  unfold BadU BadT
  rw [hq_unfold (X - 4) (a + 1), Nat.zero_add]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · right; exact ⟨hX, Or.inl (by omega)⟩
    · right; exact ⟨hX, Or.inr ⟨by omega, h2⟩⟩
  · rintro (h | ⟨-, h | ⟨h1, h2⟩⟩)
    · omega
    · left; omega
    · right; exact ⟨by omega, h2⟩

theorem badT_O (N : Nat) : BadT N 0 0 ↔ ∃ n, N = 2 ^ (n + 4) - 2 * n - 10 := by
  have e : BadT N 0 0 ↔ Hq N 0 := by
    rw [hq_unfold]; unfold BadT; simp only [Nat.mul_zero, Nat.zero_add]
  rw [e]
  constructor
  · rintro ⟨n, rfl⟩; exact ⟨n, T_zero n⟩
  · rintro ⟨n, rfl⟩; exact ⟨n, (T_zero n).symm⟩

/-! ## The two phases -/

/-- After the first passes: the left block is odd or 0. -/
def OddG (s : Q) : Prop := s.X % 2 = 1 ∨ s.X = 0

/-- During the first passes of an epoch from an even `N` that does not halt. -/
def EvenG (s : Q) : Prop :=
  s.X % 2 = 0 ∧ 2 ≤ s.X ∧ s.m = .none ∧ s.b = 0 ∧
    match s.t with
    | some r => ¬ BadT s.X s.a r
    | none => ¬ BadU s.X s.a

theorem O_cases (N : Nat) : OddG (O N) ∨ EvenG (O N) ∨ BadT N 0 0 := by
  by_cases hb : BadT N 0 0
  · exact Or.inr (Or.inr hb)
  · by_cases hp : N % 2 = 1 ∨ N = 0
    · exact Or.inl hp
    · exact Or.inr (Or.inl ⟨by simp only [O]; omega, by simp only [O]; omega, rfl, rfl, hb⟩)

theorem odd_next (s s' : Q) (n : Nat) (hs : OddG s) (hi : InvQ s) (h : mstep s = .go s' n) :
    OddG s' ∨ ∃ N, s' = O N := by
  obtain ⟨X, a, m, b, t⟩ := s
  obtain ⟨h1, -, -⟩ := hi
  simp only [OddG] at hs h1
  cases m <;> (try cases t) <;> simp only [mstep, withNorm, norm, tailNext, evNext] at h <;>
    (repeat' split at h) <;>
    (first | (simp only [MS.go.injEq] at h; obtain ⟨rfl, -⟩ := h) | cases h) <;>
    (repeat' split) <;>
    (try (by_cases hx : X - 2 = 1 <;> simp only [hx, ↓reduceIte])) <;>
    first
    | (right; exact ⟨_, rfl⟩)
    | (left; unfold OddG; dsimp only; (try omega); done)
    | omega

theorem even_next (s s' : Q) (n : Nat) (hs : EvenG s) (h : mstep s = .go s' n) : OddG s' ∨ EvenG s' := by
  obtain ⟨X, a, m, b, t⟩ := s
  obtain ⟨he, h2, hm, hb, ht⟩ := hs
  simp only at he h2 hm hb ht
  subst hm hb
  cases t with
  | some r =>
    simp only at ht
    cases r with
    | zero =>
      simp only [mstep, withNorm, norm, tailNext] at h
      repeat' split at h
      all_goals (first | (simp only [MS.go.injEq] at h; obtain ⟨rfl, -⟩ := h) | cases h)
      all_goals (repeat' split)
      all_goals (try (by_cases hx : X - 2 = 1 <;> simp only [hx, ↓reduceIte]))
      all_goals first
        | (left; unfold OddG; dsimp only; (try omega); done)
        | (right; refine ⟨by simp only; omega, by simp only; omega, rfl, rfl, ?_⟩
           simp only [Nat.add_zero]; rw [badT_zero X a (by omega)]; exact ht)
        | omega
    | succ r =>
      simp only [mstep, withNorm, norm, tailNext] at h
      repeat' split at h
      all_goals (first | (simp only [MS.go.injEq] at h; obtain ⟨rfl, -⟩ := h) | cases h)
      all_goals (repeat' split)
      all_goals (try (by_cases hx : X - 2 = 1 <;> simp only [hx, ↓reduceIte]))
      all_goals first
        | (left; unfold OddG; dsimp only; (try omega); done)
        | (right; refine ⟨by simp only; omega, by simp only; omega, rfl, rfl, ?_⟩
           simp only [Nat.add_zero]; rw [badT_succ X a r (by omega)]; exact ht)
        | omega
  | none =>
    simp only at ht
    simp only [mstep, withNorm, norm] at h
    repeat' split at h
    all_goals (first | (simp only [MS.go.injEq] at h; obtain ⟨rfl, -⟩ := h) | cases h)
    all_goals (repeat' split)
    all_goals first
      | (left; unfold OddG; dsimp only; (try omega); done)
      | (right; refine ⟨by simp only; omega, by simp only; omega, rfl, rfl, ?_⟩
         simp only [Nat.add_zero]; rw [badU_merge X a (by omega)]; exact ht)
      | omega

/-- The invariant of a run that has not passed a halting outer configuration. -/
def Good (s : Q) : Prop := InvQ s ∧ (OddG s ∨ EvenG s)

theorem good_no_halt (s : Q) (h : Good s) : mstep s ≠ .halt := by
  intro hh
  obtain ⟨h4, hm, ht⟩ := (mstep_halt_iff s).mp hh
  obtain ⟨X, a, m, b, t⟩ := s
  simp only at h4 hm ht; subst h4 hm ht
  rcases h.2 with h | ⟨-, -, -, -, h⟩
  · simp only [OddG] at h; omega
  · exact h (Or.inl rfl)

theorem good_next (s s' : Q) (n : Nat) (h : Good s) (hs : mstep s = .go s' n) : Good s' ∨ (∃ N, s' = O N ∧ BadT N 0 0) := by
  have hi := (inv_next s h.1).2 s' n hs
  have key : OddG s' ∨ EvenG s' ∨ ∃ N, s' = O N := by
    rcases h.2 with ho | he
    · rcases odd_next s s' n ho h.1 hs with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
    · rcases even_next s s' n he hs with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
  rcases key with h' | h' | ⟨N, rfl⟩
  · exact Or.inl ⟨hi, Or.inl h'⟩
  · exact Or.inl ⟨hi, Or.inr h'⟩
  · rcases O_cases N with h' | h' | h'
    · exact Or.inl ⟨hi, Or.inl h'⟩
    · exact Or.inl ⟨hi, Or.inr h'⟩
    · exact Or.inr ⟨N, rfl, h'⟩

theorem good_s0 : Good s0 := by
  refine ⟨inv_s0, Or.inr ⟨rfl, by decide, rfl, rfl, ?_⟩⟩
  show ¬ BadT 10 0 0
  rintro (h | ⟨-, n, h⟩)
  · omega
  · have := T_ge n (0 + 2 * 0 + 4); omega

/-- **Halting is a question about the outer configurations.**  The machine halts from blank tape if and only if its
run passes an outer configuration `1^N F>0 0 1^3` with `N = 2^(n+4) - 2n - 10` (6, 20, 50, 112, 238, ...). -/
theorem halts_iff_outer :
    HaltsFromBlank ↔ ∃ k t N, mrun k m0 = .go (O N) t ∧ ∃ n, N = 2 ^ (n + 4) - 2 * n - 10 := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hN
    have run : ∀ k, ∃ s t, mrun k m0 = .go s t ∧ Good s := by
      intro k
      induction k with
      | zero => exact ⟨s0, 102, rfl, good_s0⟩
      | succ k ih =>
        obtain ⟨s, t, hm, hg⟩ := ih
        rw [mrun_succ', hm]
        simp only [mnext]
        cases hst : mstep s with
        | go s' j =>
          rcases good_next s s' j hg hst with h' | ⟨N, rfl, hb⟩
          · exact ⟨s', t + j, rfl, h'⟩
          · exact absurd ⟨k + 1, t + j, N, by rw [mrun_succ', hm]; simp only [mnext, hst], (badT_O N).mp hb⟩ hN
        | halt => exact absurd hst (good_no_halt s hg)
        | stuck => exact absurd hst ((inv_next s hg.1).1)
    obtain ⟨k, hk⟩ := halts_iff.mp hH
    obtain ⟨s, t, hm, -⟩ := run k
    rw [hm] at hk; cases hk
  · rintro ⟨k, t, N, hm, n, rfl⟩
    rcases mrun_inv k with ⟨s, t', hm', -, hs⟩ | hm'
    · rw [hm] at hm'; simp only [MS.go.injEq] at hm'; obtain ⟨rfl, rfl⟩ := hm'
      exact halts_of_steps hs (outer_halts n)
    · rw [hm] at hm'; cases hm'

end H15252
