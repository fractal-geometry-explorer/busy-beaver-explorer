import Rules

/-!
# The E-pass of 1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---, for every context

An *E-event* is `c E> 1^n` (blank beyond): `EvT P n` with `P` the tape left of the head.  The E-pass halves the
block into `(01)^⌈n/2⌉`, and every two `01` are turned back into six 1s of a new block (`pairs`, iterated by
`loop`).  What is left is the context with a block of length `m = 3⌈n/2⌉ + 2`, the head in C on its first cell
(`Cn P m`); when ⌈n/2⌉ is odd one more 1 is appended to the context (`b = 1`):

    n = 4i+4  →  Cn P (6i+8)            n = 4i+3  →  Cn P (6i+8)
    n = 4i+2  →  Cn (1 P) (6i+5)        n = 4i+5  →  Cn (1 P) (6i+11)

(`pass0`, `pass3`, `pass2`, `pass1`), for **every** left tape `P`: the arithmetic of a pass does not depend on the
context.  What the context does next with the block (`Ctx.lean`) depends only on the context and the parity of m.
-/

namespace H121010

open TM

/-- A block of `n` ones, then blank tape. -/
def ones (n : Nat) : Tape := rep n [true] blank

theorem rep_tt_ones (e n : Nat) : rep e [true, true] (ones n) = ones (2 * e + n) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [rep_succ, ih, show 2 * (e + 1) + n = (2 * e + n) + 1 + 1 by omega]
    rfl

theorem tt_ones (e : Nat) : rep e [true, true] blank = ones (2 * e) := by
  have h := rep_tt_ones e 0
  rw [Nat.add_zero] at h
  exact h

theorem tt_ones' (j : Nat) : rep (j + 1) [true, true] blank = ones (2 * j + 2) := by
  rw [tt_ones, show 2 * (j + 1) = 2 * j + 2 by omega]

theorem tt_ones_odd (j : Nat) : cons true (rep (j + 2) [true, true] blank) = ones (2 * j + 5) := by
  rw [tt_ones, show 2 * j + 5 = 2 * (j + 2) + 1 by omega]
  rfl

/-- `a` reaches `b` in at least `N` steps (without a halt on the way). -/
def Reaches (a b : Config) (N : Nat) : Prop := ∃ t, N ≤ t ∧ steps t a = some b

theorem Reaches.trans' {a b c : Config} {N M : Nat} (h₁ : Reaches a b N) (h₂ : Reaches b c M) :
    Reaches a c (N + M) := by
  obtain ⟨t₁, n₁, s₁⟩ := h₁
  obtain ⟨t₂, n₂, s₂⟩ := h₂
  exact ⟨t₁ + t₂, by omega, steps_seq trans s₁ s₂⟩

theorem Reaches.mono {a b : Config} {N M : Nat} (h : Reaches a b N) (hM : M ≤ N) : Reaches a b M := by
  obtain ⟨t, n, s⟩ := h
  exact ⟨t, by omega, s⟩

theorem Reaches.refl (a : Config) : Reaches a a 0 := ⟨0, Nat.le_refl _, rfl⟩

/-- The head in C on the first cell of the last block, `m` ones. -/
def Cn (P : Tape) (m : Nat) : Config := ⟨P, ones m, .C⟩

/-- An E-event: E on the first cell of the last block, `n` ones. -/
def EvT (P : Tape) (n : Nat) : Config := ⟨P, ones n, .E⟩

/-- An E-event with context `c`, written left to right (`c` starts with the leftmost 1 of the tape). -/
def Ev (c : List Bool) (n : Nat) : Config := EvT (app c.reverse blank) n

/-- The two context rewrites of an entry of the table, for every block of the given parity. -/
def EntryOK (e : List Bool × Option (List Bool × Nat) × Option (List Bool × Nat)) : Prop :=
  (∀ c' a, e.2.1 = some (c', a) → ∀ j, Reaches (Cn (app e.1.reverse blank) (2 * j + 2)) (Ev c' (2 * j + 2 + a)) 0) ∧
  (∀ c' a, e.2.2 = some (c', a) → ∀ j,
    Reaches (Cn (cons true (app e.1.reverse blank)) (2 * j + 5)) (Ev c' (2 * j + 5 + a)) 0)

/-- `i` rounds of `pairs`: `P (01)^(2i) C> 1^(2j+2)` to `P C> 1^(2j+2+6i)`. -/
theorem loop (P : Tape) : ∀ i j : Nat,
    Reaches (Cn (rep (2 * i) [true, false] P) (2 * j + 2)) (Cn P (2 * j + 2 + 6 * i)) 0 := by
  intro i
  induction i with
  | zero => intro j; exact Reaches.refl _
  | succ i ih =>
    intro j
    have h := pairs j (rep (2 * i) [true, false] P)
    have e : cons true (cons true (cons true (cons true (cons true (cons true (cons true
        (rep j [true, true] (cons true blank)))))))) = ones (2 * (j + 3) + 2) := by
      show cons true (cons true (cons true (cons true (cons true (cons true (cons true
        (rep j [true, true] (ones 1)))))))) = _
      rw [rep_tt_ones, show 2 * (j + 3) + 2 = 2 * j + 1 + 7 by omega]
      rfl
    rw [tt_ones', e] at h
    have h₁ : Reaches (Cn (rep (2 * (i + 1)) [true, false] P) (2 * j + 2))
        (Cn (rep (2 * i) [true, false] P) (2 * (j + 3) + 2)) 0 := by
      rw [show 2 * (i + 1) = 2 + 2 * i by omega, rep_add]
      exact ⟨_, Nat.zero_le _, h⟩
    have h₂ := ih (j + 3)
    rw [show 2 * (j + 3) + 2 + 6 * i = 2 * j + 2 + 6 * (i + 1) by omega] at h₂
    exact h₁.trans' h₂

theorem ones_two : cons true (cons true blank) = ones 2 := rfl

/-- n = 4i+4: `P E> 1^(4i+4)` reaches `Cn P (6i+8)`. -/
theorem pass0 (P : Tape) (i : Nat) : Reaches (EvT P (4 * i + 4)) (Cn P (6 * i + 8)) (4 * i + 4) := by
  have h := epass_even (2 * i + 2) P
  rw [tt_ones, ones_two, show 2 * (2 * i + 2) = 4 * i + 4 by omega] at h
  have h₁ : Reaches (EvT P (4 * i + 4)) (Cn (rep (2 * (i + 1)) [true, false] P) (2 * 0 + 2)) (4 * i + 4) :=
    ⟨_, by omega, h⟩
  have h₂ := loop P (i + 1) 0
  rw [show 2 * 0 + 2 + 6 * (i + 1) = 6 * i + 8 by omega] at h₂
  exact h₁.trans' h₂

/-- n = 4i+2: `P E> 1^(4i+2)` reaches `Cn (1 P) (6i+5)`. -/
theorem pass2 (P : Tape) (i : Nat) : Reaches (EvT P (4 * i + 2)) (Cn (cons true P) (6 * i + 5)) (4 * i + 2) := by
  have h := epass_even (2 * i + 1) P
  rw [tt_ones, ones_two, show 2 * (2 * i + 1) = 4 * i + 2 by omega,
    show 2 * i + 1 = 2 * i + 1 from rfl, rep_add] at h
  have h₁ : Reaches (EvT P (4 * i + 2)) (Cn (rep (2 * i) [true, false] (rep 1 [true, false] P)) (2 * 0 + 2))
      (4 * i + 2) := ⟨_, by omega, h⟩
  have h₂ := loop (rep 1 [true, false] P) i 0
  have h₃ := one_pair (3 * i) P
  have e : cons true (cons true (cons true (cons true (rep (3 * i) [true, true] (cons true blank))))) =
      ones (6 * i + 5) := by
    show cons true (cons true (cons true (cons true (rep (3 * i) [true, true] (ones 1))))) = _
    rw [rep_tt_ones, show 6 * i + 5 = 2 * (3 * i) + 1 + 4 by omega]
    rfl
  rw [tt_ones', e] at h₃
  rw [show 2 * 0 + 2 + 6 * i = 2 * (3 * i) + 2 by omega] at h₂
  exact (h₁.trans' h₂).trans' ⟨_, Nat.zero_le _, h₃⟩

/-- The start of an odd pass: `P E> 1^(2k+3)` reaches `P (01)^k C> 1^8` (via `r_zero` and `r_zoo`). -/
theorem pass_odd (P : Tape) (k : Nat) :
    Reaches (EvT P (2 * k + 3)) (Cn (rep k [true, false] P) 8) (2 * k + 3) := by
  have h := epass_odd k P
  rw [tt_ones, show cons true (ones (2 * (k + 1))) = ones (2 * k + 3) by
    rw [show 2 * k + 3 = 2 * (k + 1) + 1 by omega]; rfl] at h
  change steps _ ⟨P, ones (2 * k + 3), .E⟩ = some ⟨cons false (cons true (cons true (cons false
    (rep k [true, false] P)))), ones 2, .C⟩ at h
  have h₂ := r_zero 0 (cons true (cons true (cons false (rep k [true, false] P))))
  change steps _ ⟨cons false (cons true (cons true (cons false (rep k [true, false] P)))), ones 2, .C⟩ =
    some ⟨cons true (cons true (cons false (rep k [true, false] P))), ones 5, .C⟩ at h₂
  have h₃ := r_zoo 1 (rep k [true, false] P)
  change steps _ ⟨cons true (cons true (cons false (rep k [true, false] P))), ones 5, .C⟩ =
    some ⟨rep k [true, false] P, ones 8, .C⟩ at h₃
  have r₁ : Reaches _ _ (2 * k + 3) := ⟨_, by omega, h⟩
  have r₂ := (r₁.trans' ⟨_, Nat.zero_le _, h₂⟩).trans' ⟨_, Nat.zero_le _, h₃⟩
  rw [Nat.add_zero, Nat.add_zero] at r₂
  exact r₂

/-- n = 4i+3: `P E> 1^(4i+3)` reaches `Cn P (6i+8)`. -/
theorem pass3 (P : Tape) (i : Nat) : Reaches (EvT P (4 * i + 3)) (Cn P (6 * i + 8)) (4 * i + 3) := by
  have h := pass_odd P (2 * i)
  rw [show 2 * (2 * i) + 3 = 4 * i + 3 by omega] at h
  have h₂ := loop P i 3
  rw [show 2 * 3 + 2 + 6 * i = 6 * i + 8 by omega] at h₂
  have h' := h.trans' h₂
  rw [Nat.add_zero] at h'
  exact h'

/-- n = 4i+5: `P E> 1^(4i+5)` reaches `Cn (1 P) (6i+11)`. -/
theorem pass1 (P : Tape) (i : Nat) : Reaches (EvT P (4 * i + 5)) (Cn (cons true P) (6 * i + 11)) (4 * i + 5) := by
  have h := pass_odd P (2 * i + 1)
  rw [show 2 * (2 * i + 1) + 3 = 4 * i + 5 by omega, rep_add] at h
  have h₂ := loop (rep 1 [true, false] P) i 3
  have h₃ := one_pair (3 * i + 3) P
  have e : cons true (cons true (cons true (cons true (rep (3 * i + 3) [true, true] (cons true blank))))) =
      ones (6 * i + 11) := by
    show cons true (cons true (cons true (cons true (rep (3 * i + 3) [true, true] (ones 1))))) = _
    rw [rep_tt_ones, show 6 * i + 11 = 2 * (3 * i + 3) + 1 + 4 by omega]
    rfl
  rw [tt_ones', e] at h₃
  rw [show 2 * 3 + 2 + 6 * i = 2 * (3 * i + 3) + 2 by omega] at h₂
  have h' := (h.trans' h₂).trans' ⟨_, Nat.zero_le _, h₃⟩
  rw [Nat.add_zero, Nat.add_zero] at h'
  exact h'

end H121010
