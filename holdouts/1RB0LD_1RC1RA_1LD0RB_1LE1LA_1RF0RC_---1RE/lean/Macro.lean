import Machine
import Rules

/-!
# The macro machine, and halting reduced to a parity question

At the start of every *phase* the tape is

    0^∞ 1^a 0 0 (1 0)^K 1^(2j+1) C> 0^∞

a *wall* of `a` ones, two 0s, `K` copies of `1 0`, and a solid block of `2j + 1` ones with the head in state C on the
blank cell after it (`enc a K j`).  One sweep (`inner`) eats two `1 0` pairs and adds six 1s to the block, so a
phase of `K / 2` sweeps ends with `K mod 2` pairs left.  Then the wall pays:

* `a ≥ 1`, `K` even: the wall loses a 1 and the block is reread as `(1 0)^(J+1) 1` (`end_even`);
* `a ≥ 1`, `K` odd: the wall loses a 1 and the block becomes `(1 0)^(J+3) 1^3` (`end_odd`);
* `a = 0`, `K` odd: the whole tape fills with 1s and becomes a new wall of `2J + 7` ones (`reset_a`, `reset_b`);
* `a = 0`, `K` even: the machine halts (`to_halt`),

with `J = j + 3 (K / 2)`.  `mstep` is this map, `mstep_sound` and `mstep_halt` prove it for all values.

While the wall lasts, `(K, j)` follows the map `g`, which does not depend on `a`; every *epoch* starts from
`(K, j) = (0, 1)` with a fresh wall `A`, so the pair at the end of an epoch is `seq A`, the `A`-th term of one fixed
sequence.  `halts_iff` is the reduction: **the machine halts from blank tape iff some epoch ends with `seq A` even**,
where the walls are `3, 25, 227097, …` (`epochs`).  Everything is checked by the kernel except `epoch3_survives`
(`native_decide`: 227,097 terms of `seq`, numbers of 132,845 bits).
-/

namespace H155226

open TM

/-! ## Tape identities -/

theorem rep_tt (j : Nat) (s : Tape) : rep j [true, true] s = rep (2 * j) [true] s := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, rep_succ, rep_succ, rep_succ, ih]
    rfl

theorem rep_tt6 (j : Nat) (s : Tape) :
    rep j [true, true] (cons true (cons true (cons true (cons true (cons true (cons true s)))))) =
      rep (j + 3) [true, true] s := by
  have h := rep_app_comm (j + 2) [true, true] s
  have h2 := rep_app_comm (j + 1) [true, true] (app [true, true] s)
  have h3 := rep_app_comm j [true, true] (app [true, true] (app [true, true] s))
  rw [← h, ← h2, ← h3]
  rfl

theorem rep_ft3 (J : Nat) (s : Tape) :
    rep J [false, true] (cons false (cons true (cons false (cons true (cons false (cons true s)))))) =
      rep (J + 3) [false, true] s := by
  have h := rep_app_comm (J + 2) [false, true] s
  have h2 := rep_app_comm (J + 1) [false, true] (app [false, true] s)
  have h3 := rep_app_comm J [false, true] (app [false, true] (app [false, true] s))
  rw [← h, ← h2, ← h3]
  rfl

theorem rep_ft1 (J : Nat) (s : Tape) :
    rep J [false, true] (cons false (cons true s)) = rep (J + 1) [false, true] s :=
  rep_app_comm J [false, true] s

theorem rep_tf_rot (J : Nat) (s : Tape) :
    rep J [true, false] (cons true s) = cons true (rep J [false, true] s) :=
  (rep_rotate J [true] [false, true] [true, false] rfl s).symm

/-! ## The encoding -/

/-- A macro configuration: wall `a`, `K` pairs `1 0`, block `1^(2j+1)`. -/
structure MC where
  a : Nat
  K : Nat
  j : Nat
  deriving DecidableEq, Repr

/-- The wall and the two 0s after it, as seen from the right (nearest the head first). -/
def wall (a : Nat) : Tape := cons false (cons false (rep a [true] blank))

/-- `0^∞ 1^a 0 0 (1 0)^K 1^(2j+1) C> 0^∞`. -/
def enc (M : MC) : Config :=
  ⟨cons true (rep M.j [true, true] (rep M.K [false, true] (wall M.a))), blank, .C⟩

/-! ## A phase -/

/-- `i` sweeps: `(1 0)^(2i+K) 1^(2j+1) C>` becomes `(1 0)^K 1^(2j+6i+1) C>`, for every tape `L` further left. -/
theorem sweeps (i : Nat) : ∀ (j K : Nat) (L : Tape), ∃ s,
    steps s ⟨cons true (rep j [true, true] (rep (2 * i + K) [false, true] L)), blank, .C⟩ =
      some ⟨cons true (rep (j + 3 * i) [true, true] (rep K [false, true] L)), blank, .C⟩ := by
  induction i with
  | zero => intro j K L; exact ⟨0, by simp⟩
  | succ i ih =>
    intro j K L
    have h1 := inner j (2 * i + K) L
    rw [show 2 * i + K + 2 = 2 * (i + 1) + K by omega, rep_tt6] at h1
    obtain ⟨s, h2⟩ := ih (j + 3) K L
    rw [show j + 3 + 3 * i = j + 3 * (i + 1) by omega] at h2
    exact ⟨_, steps_seq trans h1 h2⟩

/-- The macro step: one phase, from one phase start to the next; `none` when the machine halts. -/
def mstep (M : MC) : Option MC :=
  if M.K % 2 = 0 then
    match M.a with
    | 0 => none
    | a + 1 => some ⟨a, M.j + 3 * (M.K / 2) + 1, 0⟩
  else
    match M.a with
    | 0 => some ⟨2 * (M.j + 3 * (M.K / 2)) + 7, 0, 1⟩
    | a + 1 => some ⟨a, M.j + 3 * (M.K / 2) + 3, 1⟩

theorem mstep_sound (M M' : MC) (h : mstep M = some M') : ∃ s, 0 < s ∧ steps s (enc M) = some (enc M') := by
  obtain ⟨a, K, j⟩ := M
  unfold mstep at h
  simp only at h
  by_cases hK : K % 2 = 0
  · rw [if_pos hK] at h
    obtain ⟨s, hs⟩ := sweeps (K / 2) j 0 (wall a)
    rw [show 2 * (K / 2) + 0 = K by omega] at hs
    cases a with
    | zero => cases h
    | succ a =>
      simp only [Option.some.injEq] at h
      subst h
      have h2 := end_even (j + 3 * (K / 2)) (rep a [true] blank)
      rw [rep_tf_rot, rep_ft1] at h2
      refine ⟨_, ?_, steps_seq trans hs h2⟩; omega
  · rw [if_neg hK] at h
    obtain ⟨s, hs⟩ := sweeps (K / 2) j 1 (wall a)
    rw [show 2 * (K / 2) + 1 = K by omega] at hs
    cases a with
    | zero =>
      simp only [Option.some.injEq] at h
      subst h
      have h2 := reset_a (j + 3 * (K / 2))
      have h3 := reset_b (rep (2 * (j + 3 * (K / 2)) + 7) [true] blank)
      have e : rep (j + 3 * (K / 2)) [true, true]
          (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true blank))))))))
          = cons true (rep (2 * (j + 3 * (K / 2)) + 7) [true] blank) := by
        rw [rep_tt, show (cons true (cons true (cons true (cons true (cons true (cons true (cons true
          (cons true blank)))))))) = rep 8 [true] blank from rfl, ← rep_add,
          show 2 * (j + 3 * (K / 2)) + 8 = (2 * (j + 3 * (K / 2)) + 7) + 1 by omega]
        rfl
      rw [e] at h2
      refine ⟨_, ?_, steps_seq trans hs (steps_seq trans h2 h3)⟩; omega
    | succ a =>
      simp only [Option.some.injEq] at h
      subst h
      have h2 := end_odd (j + 3 * (K / 2)) (rep a [true] blank)
      rw [rep_ft3] at h2
      refine ⟨_, ?_, steps_seq trans hs h2⟩; omega

theorem mstep_halt (M : MC) (h : mstep M = none) : Halts trans (enc M) := by
  obtain ⟨a, K, j⟩ := M
  unfold mstep at h
  simp only at h
  by_cases hK : K % 2 = 0
  · rw [if_pos hK] at h
    cases a with
    | succ a => cases h
    | zero =>
      obtain ⟨s, hs⟩ := sweeps (K / 2) j 0 (wall 0)
      rw [show 2 * (K / 2) + 0 = K by omega] at hs
      exact ⟨_, _, steps_seq trans hs (to_halt (j + 3 * (K / 2))), rfl⟩
  · rw [if_neg hK] at h
    cases a <;> cases h

/-! ## Halting as a property of an orbit -/

/-- `t` steps of a partial map. -/
def orbit {α : Type} (f : α → Option α) : Nat → α → Option α
  | 0, x => some x
  | t + 1, x => (orbit f t x).bind f

/-- A macro machine `f` on an encoding `E` that is sound (every step is at least one machine step) and whose stuck
points halt: the machine halts from `c₀ ⟶ E x₀` iff the orbit of `x₀` gets stuck. -/
theorem halts_iff_orbit {α : Type} (E : α → Config) (f : α → Option α)
    (hs : ∀ x y, f x = some y → ∃ s, 0 < s ∧ steps s (E x) = some (E y))
    (hn : ∀ x, f x = none → Halts trans (E x))
    (c₀ : Config) (x₀ : α) (s₀ : Nat) (h₀ : steps s₀ c₀ = some (E x₀)) :
    Halts trans c₀ ↔ ∃ t x, orbit f t x₀ = some x ∧ f x = none := by
  have reach : ∀ t x, orbit f t x₀ = some x → ∃ s, s₀ + t ≤ s ∧ steps s c₀ = some (E x) := by
    intro t
    induction t with
    | zero => intro x hx; cases hx; exact ⟨s₀, by omega, h₀⟩
    | succ t ih =>
      intro x hx
      simp only [orbit] at hx
      cases ht : orbit f t x₀ with
      | none => rw [ht] at hx; cases hx
      | some y =>
        rw [ht] at hx
        obtain ⟨s, hle, hs1⟩ := ih y ht
        obtain ⟨s', hpos, hs2⟩ := hs y x hx
        exact ⟨s + s', by omega, steps_seq trans hs1 hs2⟩
  constructor
  · intro hh
    refine Classical.byContradiction fun hno => ?_
    have all : ∀ t, ∃ x, orbit f t x₀ = some x := by
      intro t
      induction t with
      | zero => exact ⟨x₀, rfl⟩
      | succ t ih =>
        obtain ⟨y, hy⟩ := ih
        cases hf : f y with
        | none => exact absurd ⟨t, y, hy, hf⟩ hno
        | some z => exact ⟨z, by simp only [orbit, hy]; exact hf⟩
    apply not_halts_of_forall trans _ hh
    intro n
    obtain ⟨x, hx⟩ := all n
    obtain ⟨s, hle, hs1⟩ := reach n x hx
    rw [show s = n + (s - n) by omega] at hs1
    exact steps_le trans hs1
  · rintro ⟨t, x, hx, hf⟩
    obtain ⟨s, -, hs1⟩ := reach t x hx
    obtain ⟨n, c', h1, h2⟩ := hn x hf
    exact ⟨s + n, c', steps_seq trans hs1 h1, h2⟩

/-- The first phase start, 18 steps from blank tape: `1^3 0 0 1^3 C>`. -/
def M0 : MC := ⟨3, 0, 1⟩

theorem init_M0 : steps 18 init = some (enc M0) := start

/-- **Halting reduced to the macro machine**, phase by phase. -/
theorem halts_iff_mstep : HaltsFromBlank ↔ ∃ t M, orbit mstep t M0 = some M ∧ mstep M = none :=
  halts_iff_orbit enc mstep mstep_sound mstep_halt init M0 18 init_M0

/-! ## Epochs: one fixed sequence, sampled at the walls -/

/-- One phase on `(K, j)` while the wall lasts. -/
def g (x : Nat × Nat) : Nat × Nat :=
  if x.1 % 2 = 0 then (x.2 + 3 * (x.1 / 2) + 1, 0) else (x.2 + 3 * (x.1 / 2) + 3, 1)

/-- `n` phases. -/
def giter : Nat → Nat × Nat → Nat × Nat
  | 0, x => x
  | n + 1, x => giter n (g x)

/-- The sequence every epoch follows: `seq i` is `(K, j)` after `i` phases from `(0, 1)`. -/
def seq (i : Nat) : Nat × Nat := giter i (0, 1)

/-- The wall of the next epoch, or `none` if this epoch ends with `K` even (a halt). -/
def nextWall (A : Nat) : Option Nat :=
  let x := seq A
  if x.1 % 2 = 0 then none else some (2 * (x.2 + 3 * (x.1 / 2)) + 7)

/-- An epoch start: wall `A`, no pairs, block `1^3`. -/
def encE (A : Nat) : Config := enc ⟨A, 0, 1⟩

theorem walk (A : Nat) : ∀ x : Nat × Nat, ∃ s,
    steps s (enc ⟨A, x.1, x.2⟩) = some (enc ⟨0, (giter A x).1, (giter A x).2⟩) := by
  induction A with
  | zero => intro x; exact ⟨0, rfl⟩
  | succ A ih =>
    intro x
    have hm : mstep ⟨A + 1, x.1, x.2⟩ = some ⟨A, (g x).1, (g x).2⟩ := by
      unfold mstep g
      by_cases h : x.1 % 2 = 0 <;> simp [h]
    obtain ⟨s, -, hs⟩ := mstep_sound _ _ hm
    obtain ⟨s', hs'⟩ := ih (g x)
    exact ⟨s + s', steps_seq trans hs hs'⟩

theorem epoch_sound (A A' : Nat) (h : nextWall A = some A') : ∃ s, 0 < s ∧ steps s (encE A) = some (encE A') := by
  obtain ⟨s, hs⟩ := walk A (0, 1)
  have hm : mstep ⟨0, (seq A).1, (seq A).2⟩ = some ⟨A', 0, 1⟩ := by
    unfold nextWall at h
    unfold mstep
    by_cases hK : (seq A).1 % 2 = 0
    · simp [hK] at h
    · simp only [hK] at h ⊢
      simp at h
      simp [h]
  obtain ⟨s', hpos, hs'⟩ := mstep_sound _ _ hm
  exact ⟨s + s', by omega, steps_seq trans hs hs'⟩

theorem epoch_halt (A : Nat) (h : nextWall A = none) : Halts trans (encE A) := by
  obtain ⟨s, hs⟩ := walk A (0, 1)
  have hm : mstep ⟨0, (seq A).1, (seq A).2⟩ = none := by
    unfold nextWall at h
    unfold mstep
    by_cases hK : (seq A).1 % 2 = 0
    · simp [hK]
    · simp [hK] at h
  obtain ⟨n, c', h1, h2⟩ := mstep_halt _ hm
  exact ⟨s + n, c', steps_seq trans hs h1, h2⟩

/-- The walls of the epochs: `epochs 0 = some 3`, then `nextWall`. -/
def epochs (i : Nat) : Option Nat := orbit nextWall i 3

/-- **The machine halts from blank tape iff some epoch ends with an even `K`:** iff for some `i` the wall
`A = epochs i` exists and `(seq A).1` is even. -/
theorem halts_iff : HaltsFromBlank ↔ ∃ i A, epochs i = some A ∧ (seq A).1 % 2 = 0 := by
  show Halts trans init ↔ _
  rw [halts_iff_orbit encE nextWall epoch_sound epoch_halt init 3 18 init_M0]
  constructor
  · rintro ⟨t, A, h1, h2⟩
    refine ⟨t, A, h1, ?_⟩
    unfold nextWall at h2
    by_cases hK : (seq A).1 % 2 = 0
    · exact hK
    · simp [hK] at h2
  · rintro ⟨t, A, h1, h2⟩
    exact ⟨t, A, h1, by unfold nextWall; simp [h2]⟩

/-- The first two epochs, by the kernel: walls 3, 25, 227097. -/
theorem epochs_small : epochs 1 = some 25 ∧ epochs 2 = some 227097 := by decide

end H155226
