import Core.Rules

/-!
# Configurations of the core, and the drain of the halved block

An *E-event* is `c E> 1^n` (blank beyond): `Ev c n`, with `c` the tape from its first 1 up to the head.  `Cn P m`
is the head in C on the first cell of a block of `m` ones.  `drain`: `P (01)^q C> 1^(2u+2)` reaches `Cq P q m` with
m = 2u + 2 + 3q, where `Cq P q m` is `P C> 1^m` for q even and `P 1 C> 1^m` for q odd: every two `01` become six
more 1s (`pairs`, `loop`), an odd one left over becomes one more 1 of the context (`one_pair`).  None of this reads
F0, so it holds for every `f0`.
-/

namespace Core

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

/-- The head in C on the first cell of the last block, `m` ones. -/
def Cn (P : Tape) (m : Nat) : Config := ⟨P, ones m, .C⟩

/-- An E-event: E on the first cell of the last block, `n` ones. -/
def EvT (P : Tape) (n : Nat) : Config := ⟨P, ones n, .E⟩

/-- An E-event with context `c`, written left to right (`c` starts with the leftmost 1 of the tape). -/
def Ev (c : List Bool) (n : Nat) : Config := EvT (app c.reverse blank) n

/-- The end of a pass: `P C> 1^m` if `q` is even, `P 1 C> 1^m` if `q` is odd. -/
def Cq (P : Tape) (q m : Nat) : Config := if q % 2 = 0 then Cn P m else Cn (cons true P) m

section
variable (f0 : Bool × Dir × St)

/-- `a` reaches `b` in at least `N` steps (without a halt on the way). -/
def Reaches (a b : Config) (N : Nat) : Prop := ∃ t, N ≤ t ∧ steps f0 t a = some b

variable {f0}

theorem Reaches.trans' {a b c : Config} {N M : Nat} (h₁ : Reaches f0 a b N) (h₂ : Reaches f0 b c M) :
    Reaches f0 a c (N + M) := by
  obtain ⟨t₁, n₁, s₁⟩ := h₁
  obtain ⟨t₂, n₂, s₂⟩ := h₂
  exact ⟨t₁ + t₂, by omega, steps_seq (trans f0) s₁ s₂⟩

theorem Reaches.refl (a : Config) : Reaches f0 a a 0 := ⟨0, Nat.le_refl _, rfl⟩

theorem halts_of_reaches {a b : Config} {N : Nat} (r : Reaches f0 a b N) (h : Halts (trans f0) b) :
    Halts (trans f0) a := by
  obtain ⟨t, _, s⟩ := r
  obtain ⟨n, c, s', hc⟩ := h
  exact ⟨t + n, c, steps_seq (trans f0) s s', hc⟩

variable (f0)

/-- `i` rounds of `pairs`: `P (01)^(2i) C> 1^(2j+2)` to `P C> 1^(2j+2+6i)`. -/
theorem loop (P : Tape) : ∀ i j : Nat,
    Reaches f0 (Cn (rep (2 * i) [true, false] P) (2 * j + 2)) (Cn P (2 * j + 2 + 6 * i)) 0 := by
  intro i
  induction i with
  | zero => intro j; exact Reaches.refl _
  | succ i ih =>
    intro j
    have h := pairs f0 j (rep (2 * i) [true, false] P)
    have e : cons true (cons true (cons true (cons true (cons true (cons true (cons true
        (rep j [true, true] (cons true blank)))))))) = ones (2 * (j + 3) + 2) := by
      show cons true (cons true (cons true (cons true (cons true (cons true (cons true
        (rep j [true, true] (ones 1)))))))) = _
      rw [rep_tt_ones, show 2 * (j + 3) + 2 = 2 * j + 1 + 7 by omega]
      rfl
    rw [tt_ones', e] at h
    have h₁ : Reaches f0 (Cn (rep (2 * (i + 1)) [true, false] P) (2 * j + 2))
        (Cn (rep (2 * i) [true, false] P) (2 * (j + 3) + 2)) 0 := by
      rw [show 2 * (i + 1) = 2 + 2 * i by omega, rep_add]
      exact ⟨_, Nat.zero_le _, h⟩
    have h₂ := ih (j + 3)
    rw [show 2 * (j + 3) + 2 + 6 * i = 2 * j + 2 + 6 * (i + 1) by omega] at h₂
    exact h₁.trans' h₂

/-- The halved block drains: `P (01)^q C> 1^(2u+2)` reaches `Cq P q (2u+2+3q)`. -/
theorem drain (P : Tape) (q u : Nat) :
    Reaches f0 (Cn (rep q [true, false] P) (2 * u + 2)) (Cq P q (2 * u + 2 + 3 * q)) 0 := by
  obtain ⟨i, hi⟩ : ∃ i, q = 2 * i ∨ q = 2 * i + 1 := ⟨q / 2, by omega⟩
  rcases hi with rfl | rfl
  · have h := loop f0 P i u
    have hq : (2 * i) % 2 = 0 := by omega
    simp only [Cq, hq, ↓reduceIte]
    rw [show 2 * u + 2 + 3 * (2 * i) = 2 * u + 2 + 6 * i by omega]
    exact h
  · have hq : (2 * i + 1) % 2 = 1 := by omega
    simp only [Cq, hq, show (1 : Nat) ≠ 0 from by decide, ↓reduceIte]
    rw [rep_add]
    have h₂ := loop f0 (rep 1 [true, false] P) i u
    have h₃ := one_pair f0 (u + 3 * i) P
    have e : cons true (cons true (cons true (cons true (rep (u + 3 * i) [true, true] (cons true blank))))) =
        ones (2 * u + 2 + 3 * (2 * i + 1)) := by
      show cons true (cons true (cons true (cons true (rep (u + 3 * i) [true, true] (ones 1))))) = _
      rw [rep_tt_ones, show 2 * u + 2 + 3 * (2 * i + 1) = 2 * (u + 3 * i) + 1 + 4 by omega]
      rfl
    rw [tt_ones', e] at h₃
    rw [show 2 * u + 2 + 6 * i = 2 * (u + 3 * i) + 2 by omega] at h₂
    have h' := h₂.trans' (⟨_, Nat.zero_le _, h₃⟩ : Reaches f0 _ (Cn (cons true P) _) 0)
    rw [Nat.add_zero] at h'
    exact h'

/-- What a context does with the block, for both parities: the next E-event (`some (c', a)`: block m becomes an
E-event with context c' and m + a ones) or a halt (`none`). -/
def EntryOK (e : List Bool × Option (List Bool × Nat) × Option (List Bool × Nat)) : Prop :=
  (match e.2.1 with
   | some (c', a) => ∀ j, Reaches f0 (Cn (app e.1.reverse blank) (2 * j + 2)) (Ev c' (2 * j + 2 + a)) 0
   | none => ∀ j, Halts (trans f0) (Cn (app e.1.reverse blank) (2 * j + 2))) ∧
  (match e.2.2 with
   | some (c', a) => ∀ j, Reaches f0 (Cn (cons true (app e.1.reverse blank)) (2 * j + 5)) (Ev c' (2 * j + 5 + a)) 0
   | none => ∀ j, Halts (trans f0) (Cn (cons true (app e.1.reverse blank)) (2 * j + 5)))

end

end Core
