import Rules

/-!
# Antihydra as a walk: the machine halts exactly when the walk does

From blank tape the run passes through the configurations

  `Q p a b  =  0^∞ 1^p 0 1^a 0 1^b B> 0^∞`

(three blocks of ones, the head in state B on the blank cell right of the last).  Lean proves, for every `p`, `a`,
`b` (kernel only):

* `sweep`: `Q p (a + 2k + 1) (b + 1)` reaches `Q p (a + 1) (b + 1 + 3k)`: each sweep moves 2 ones out of the middle
  block and writes 3 onto the right block (`inner` in `Rules.lean`);
* when the middle block is down to 1 (`a` odd) the left block gains 2 (`odd_end`); when it is down to 2 (`a` even)
  the left block loses 1 (`even_end`), or, if there is no left block, the machine halts (`halt_end`).

So with `b = 2`, `Q p a 2` goes to `Q p' a' 2` with `nxt (p, a) = (p', a')`: `a = 2k + 1` gives `(p + 2, 3k + 4)`,
`a = 2k + 2` gives `(p - 1, 3k + 5)`, and `a` even with `p = 0` halts.  After 62 steps from blank tape the run is at
`Q 2 7 2` (`blank_to_Q`).  `halts_iff`: the machine halts from blank tape if and only if the orbit of `(2, 7)`
under `nxt` reaches the halting case.  With `x = a + 5` this is the map `x ↦ ⌊3x/2⌋` with a counter that goes up 2
when `x` is even and down 1 when `x` is odd: the Collatz-like problem known as Antihydra, which is open.
-/

namespace H9785

open TM

/-- `0^∞ 1^p 0 1^a 0 1^b B> 0^∞`. -/
def Q (p a b : Nat) : Config :=
  ⟨rep b [true] (cons false (rep a [true] (cons false (rep p [true] blank)))), blank, .B⟩

/-- A run of at least one step from `c` ends at `c'`. -/
def R (c c' : Config) : Prop := ∃ n, 0 < n ∧ steps n c = some c'

theorem R.trans {a b c : Config} (h₁ : R a b) (h₂ : R b c) : R a c := by
  obtain ⟨n₁, p₁, h₁⟩ := h₁
  obtain ⟨n₂, _, h₂⟩ := h₂
  exact ⟨n₁ + n₂, by omega, steps_seq H9785.trans h₁ h₂⟩

theorem R.of {n : Nat} {c c' : Config} (h : steps (n + 1) c = some c') : R c c' := ⟨n + 1, by omega, h⟩

theorem R.of' {n : Nat} {c c' : Config} (hn : 0 < n) (h : steps n c = some c') : R c c' := ⟨n, hn, h⟩

theorem ones_cons (n : Nat) (s : Tape) : rep n [true] (cons true s) = cons true (rep n [true] s) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep_succ, app_cons, app_nil, ih]

/-- One sweep: the middle block loses 2, the right block gains 3. -/
theorem sweep_one (p a b : Nat) : R (Q p (a + 3) (b + 1)) (Q p (a + 1) (b + 4)) := by
  have h := inner a b (rep p [true] blank)
  simp only [ones_cons] at h
  exact R.of' (by omega) h

/-- `k ≥ 1` sweeps. -/
theorem sweep' (p k : Nat) : ∀ a b, 0 < k → R (Q p (a + 2 * k + 1) (b + 1)) (Q p (a + 1) (b + 1 + 3 * k)) := by
  induction k with
  | zero => intro a b h; exact absurd h (by omega)
  | succ k ih =>
    intro a b _
    have h₁ := sweep_one p (a + 2 * k) b
    rw [show a + 2 * k + 3 = a + 2 * (k + 1) + 1 by omega] at h₁
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simpa using h₁
    · have h₂ := ih a (b + 3) hk
      rw [show b + 3 + 1 = b + 4 by omega, show b + 3 + 1 + 3 * k = b + 1 + 3 * (k + 1) by omega] at h₂
      exact h₁.trans h₂

theorem cfb : cons false blank = blank := cons_false_blank

/-- Middle block 1: the left block gains 2 and the right block becomes the middle block. -/
theorem odd_end (p c : Nat) : R (Q p 1 (c + 2)) (Q (p + 2) (c + 4) 2) := by
  cases p with
  | zero =>
    have h := odd0 c
    simp only [ones_cons] at h
    have e : Q 0 1 (c + 2) = ⟨cons true (cons true (rep c [true] (cons false (cons true blank)))), blank, .B⟩ := by
      simp only [Q, rep_succ, rep_zero, app_cons, app_nil, cfb]
    rw [e]
    have e2 : Q (0 + 2) (c + 4) 2 = ⟨cons true (cons true (cons false (cons true (cons true (cons true (cons true
        (rep c [true] (cons false (cons true (cons true blank)))))))))), blank, .B⟩ := by
      simp only [Q, rep_succ, rep_zero, app_cons, app_nil]
    rw [e2]
    exact R.of' (by omega) h
  | succ p =>
    have h₁ := odd_a c p
    have h₂ := odd_b c p
    simp only [ones_cons] at h₁ h₂
    have h := steps_seq trans h₁ h₂
    have e2 : Q (p + 1 + 2) (c + 4) 2 = ⟨cons true (cons true (cons false (cons true (cons true (cons true (cons true
        (rep c [true] (cons false (cons true (cons true (cons true (rep p [true] blank)))))))))))), blank, .B⟩ := by
      simp only [Q, rep_succ, rep_zero, app_cons, app_nil]
    rw [e2]
    exact R.of' (by omega) h

/-- Middle block 2 with a left block: the left block loses 1 and the right block becomes the middle block. -/
theorem even_end (p c : Nat) : R (Q (p + 1) 2 (c + 2)) (Q p (c + 5) 2) := by
  have h := even c p
  simp only [ones_cons] at h
  have e2 : Q p (c + 5) 2 = ⟨cons true (cons true (cons false (cons true (cons true (cons true (cons true (cons true
      (rep c [true] (cons false (rep p [true] blank)))))))))), blank, .B⟩ := by
    simp only [Q, rep_succ, rep_zero, app_cons, app_nil]
  rw [e2]
  exact R.of' (by omega) h

/-- Middle block 2 and no left block: the machine halts. -/
theorem halt_end (c : Nat) : ∃ n c', steps n (Q 0 2 (c + 2)) = some c' ∧ step c' = none := by
  have h := halt0 c
  have e : Q 0 2 (c + 2) = ⟨cons true (cons true (rep c [true] (cons false (cons true (cons true blank))))), blank,
      .B⟩ := by
    simp only [Q, rep_succ, rep_zero, app_cons, app_nil, cfb]
  rw [e]
  exact ⟨_, _, h, rfl⟩

/-! ## The walk -/

/-- One macro step on `(p, a)`; `none` is the halting case (`a` even, `p = 0`). -/
def nxt (x : Nat × Nat) : Option (Nat × Nat) :=
  if x.2 % 2 = 1 then some (x.1 + 2, 3 * (x.2 / 2) + 4)
  else if x.1 = 0 then none else some (x.1 - 1, 3 * (x.2 / 2) + 2)

theorem nxt_sound (p a p' a' : Nat) (ha : 2 ≤ a) (h : nxt (p, a) = some (p', a')) :
    R (Q p a 2) (Q p' a' 2) ∧ 2 ≤ a' := by
  unfold nxt at h
  by_cases h1 : a % 2 = 1
  · -- a odd, a = 2k + 3
    simp only [h1, ↓reduceIte] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨k, rfl⟩ : ∃ k, a = 2 * (k + 1) + 1 := ⟨a / 2 - 1, by omega⟩
    refine ⟨?_, by omega⟩
    have h₁ := sweep' p (k + 1) 0 1 (by omega)
    rw [show 0 + 2 * (k + 1) + 1 = 2 * (k + 1) + 1 by omega, show 1 + 1 + 3 * (k + 1) = 3 * k + 3 + 2 by omega,
      show (1 + 1 : Nat) = 2 from rfl, show (0 + 1 : Nat) = 1 from rfl] at h₁
    have h₂ := odd_end p (3 * k + 3)
    rw [show 3 * k + 3 + 4 = 3 * ((2 * (k + 1) + 1) / 2) + 4 by omega] at h₂
    exact h₁.trans h₂
  · simp only [h1, ↓reduceIte] at h
    by_cases h2 : p = 0
    · simp only [h2, ↓reduceIte] at h; cases h
    · simp only [h2, ↓reduceIte] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k + 2 := ⟨a / 2 - 1, by omega⟩
      refine ⟨?_, by omega⟩
      have h₂ := even_end q (3 * k)
      rw [show 3 * k + 5 = 3 * ((2 * k + 2) / 2) + 2 by omega] at h₂
      rw [show q + 1 - 1 = q by omega]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        exact h₂
      · have h₁ := sweep' (q + 1) k 1 1 hk
        rw [show 1 + 2 * k + 1 = 2 * k + 2 by omega, show 1 + 1 + 3 * k = 3 * k + 2 by omega,
          show (1 + 1 : Nat) = 2 from rfl] at h₁
        exact h₁.trans h₂

theorem nxt_halt (p a : Nat) (ha : 2 ≤ a) (h : nxt (p, a) = none) :
    ∃ n c', steps n (Q p a 2) = some c' ∧ step c' = none := by
  unfold nxt at h
  by_cases h1 : a % 2 = 1
  · simp only [h1, ↓reduceIte] at h; cases h
  · simp only [h1, ↓reduceIte] at h
    by_cases h2 : p = 0
    · subst h2
      obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k + 2 := ⟨a / 2 - 1, by omega⟩
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        exact halt_end 0
      · obtain ⟨n₁, _, h₁⟩ := sweep' 0 k 1 1 hk
        rw [show 1 + 2 * k + 1 = 2 * k + 2 by omega, show 1 + 1 + 3 * k = 3 * k + 2 by omega,
          show (1 + 1 : Nat) = 2 from rfl] at h₁
        obtain ⟨n₂, c', h₂, hc⟩ := halt_end (3 * k)
        exact ⟨n₁ + n₂, c', steps_seq trans h₁ h₂, hc⟩
    · simp only [h2, ↓reduceIte] at h; cases h

/-- The orbit of `(2, 7)`, the macro configuration reached after 62 steps. -/
def orbit : Nat → Option (Nat × Nat)
  | 0 => some (2, 7)
  | n + 1 => (orbit n).bind nxt

/-- After 62 steps from blank tape the run is at `Q 2 7 2`. -/
theorem blank_to_Q : steps 62 init = some (Q 2 7 2) :=
  blank_reaches trans (c := ⟨[true, true, false, true, true, true, true, true, true, true, false, true, true], [],
    .B⟩) (by decide +kernel)

/-- Every point of the orbit is reached, by a run of at least `n` steps, with a middle block of at least 2. -/
theorem orbit_reached (n : Nat) (p a : Nat) (h : orbit n = some (p, a)) :
    2 ≤ a ∧ ∃ m, n ≤ m ∧ steps m init = some (Q p a 2) := by
  induction n generalizing p a with
  | zero =>
    simp only [orbit, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, 62, by omega, blank_to_Q⟩
  | succ n ih =>
    simp only [orbit] at h
    cases e : orbit n with
    | none => rw [e] at h; cases h
    | some x =>
      obtain ⟨p₀, a₀⟩ := x
      rw [e] at h
      obtain ⟨ha₀, m, hm, hrun⟩ := ih p₀ a₀ e
      obtain ⟨⟨k, hk, hs⟩, ha⟩ := nxt_sound p₀ a₀ p a ha₀ h
      exact ⟨ha, m + k, by omega, steps_seq trans hrun hs⟩

/-- **The machine halts from blank tape if and only if the Antihydra walk reaches its halting case.** -/
theorem halts_iff : HaltsFromBlank ↔ ∃ n, orbit n = none := by
  constructor
  · intro hh
    refine Classical.byContradiction fun hne => ?_
    have hall : ∀ n, ∃ x, orbit n = some x := by
      intro n
      cases e : orbit n with
      | none => exact absurd ⟨n, e⟩ hne
      | some x => exact ⟨x, rfl⟩
    apply not_halts_of_forall trans _ hh
    apply forall_of_unbounded trans (fun m => ∃ c', steps m init = some c')
    · intro n
      obtain ⟨⟨p, a⟩, hx⟩ := hall n
      obtain ⟨_, m, hm, hrun⟩ := orbit_reached n p a hx
      exact ⟨m, hm, _, hrun⟩
    · intro m hm; exact hm
  · rintro ⟨n, hn⟩
    -- the first `none` comes right after a `some`
    induction n with
    | zero => cases hn
    | succ n ih =>
      cases e : orbit n with
      | none => exact ih e
      | some x =>
        obtain ⟨p, a⟩ := x
        simp only [orbit, e, Option.bind_some] at hn
        obtain ⟨ha, m, _, hrun⟩ := orbit_reached n p a e
        obtain ⟨k, c', hs, hc⟩ := nxt_halt p a ha hn
        exact ⟨m + k, c', steps_seq trans hrun hs, hc⟩

end H9785
