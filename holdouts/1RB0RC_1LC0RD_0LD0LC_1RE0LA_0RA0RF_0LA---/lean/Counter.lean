import Machine
import Pieces

/-!
# The counter: one visit is one increment

At a *sample configuration* the head, in state A, reads the leftmost cell of the tape, and the tape is

    0 0 W^g₀ X₁ W^g₁ X₂ W^g₂ … Xₖ W^gₖ T          W = 0 0 0 1

(`sample g₀ [(X₁, g₁), …, (Xₖ, gₖ)] T`): a *left gap* of `g₀` copies of `W`, then *digits* `Xᵢ`, each followed by a gap
of `gᵢ` copies of `W`, then an arbitrary rest `T`.  The digits are the five words

    a = 0011   b = 0011001   c = 001101   d = 00111   e = 00101

with values a = 1, b = 2, c = 3, d = 4, e = 0, the first digit the least significant.  One *visit* (the head goes right
and comes back to the left end, in state A again) adds one to this base-5 number: every leading `d` (value 4) becomes
`e` (value 0, a carry), the first other digit `X` takes the increment, and the head turns there.  `bump` is that map on
the numbers; it also moves the gaps:

* `a → b` and `e → a` take one `W` from the gap after the digit;
* `e → a` gives one `W` to the gap before it (the left gap when the digit is the first);
* every visit adds one `W` to the left gap (the tape grows by three cells on the left).

`bump` is undefined when the carry runs into `T` or the digit that takes the increment has an empty gap after it
(`gᵢ = 0`): those are the *collisions*, which this file does not cover.  `visit` is proved for every list of digits,
every gap and every rest of the tape by Lean's kernel, from the nine piece rules of `Pieces.lean`; the step count is
exact.
-/

namespace H59221

open TM

/-- The background word `0 0 0 1`. -/
abbrev W : List Bool := [false, false, false, true]

/-- The five digits. -/
inductive Dg where
  | a | b | c | d | e
  deriving DecidableEq, Repr

/-- The cells of a digit. -/
def Dg.word : Dg → List Bool
  | .a => [false, false, true, true]
  | .b => [false, false, true, true, false, false, true]
  | .c => [false, false, true, true, false, true]
  | .d => [false, false, true, true, true]
  | .e => [false, false, true, false, true]

/-- Digits, each with the gap after it, then the rest of the tape. -/
def enc : List (Dg × Nat) → Tape → Tape
  | [], T => T
  | (x, g) :: xs, T => app x.word (rep g W (enc xs T))

/-- A sample configuration: the head on the leftmost cell, blank tape to its left. -/
def sample (g : Nat) (xs : List (Dg × Nat)) (T : Tape) : Config :=
  ⟨blank, app [false, false] (rep g W (enc xs T)), .A⟩

/-- The head arriving at a digit, moving right; `L` is what it has crossed. -/
def arr (L R : Tape) : Config := ⟨cons true L, app [false, false, true] R, .E⟩

/-- The head moving left after its turn. -/
def ret (L R : Tape) : Config := ⟨app [true, false, true] L, app [false, false] R, .A⟩

/-- The increment: `some (δ, xs')` with `δ` the number of `W`s added before the digits (0 or 1). -/
def bump : List (Dg × Nat) → Option (Nat × List (Dg × Nat))
  | [] => none
  | (.d, h) :: xs =>
    match bump xs with
    | some (δ, ys) => some (0, (.e, h + δ) :: ys)
    | none => none
  | (.a, h + 1) :: xs => some (0, (.b, h) :: xs)
  | (.b, h + 1) :: xs => some (0, (.c, h + 1) :: xs)
  | (.c, h + 1) :: xs => some (0, (.d, h + 1) :: xs)
  | (.e, h + 1) :: xs => some (1, (.a, h) :: xs)
  | (_, 0) :: _ => none

/-- The steps from the arrival at the first digit to the return to the left of it. -/
def cost : List (Dg × Nat) → Nat
  | (.d, h) :: xs => 10 * h + 24 + cost xs
  | _ => 24

/-! ## The pieces, restated on the encoding -/

/-- A re-bracketing the generated rules sometimes leave: `(1010)^n 1 = 1 (0101)^n` read from the head. -/
theorem rot1 (n : Nat) (s : Tape) :
    rep n [true, false, true, false] (cons true s) = cons true (rep n [false, true, false, true] s) :=
  (rep_rotate n [true] [false, true, false, true] [true, false, true, false] rfl s).symm

theorem p_start (n : Nat) (R : Tape) :
    steps (4 * n + 5) ⟨blank, app [false, false] (rep n W R), .A⟩ = some (arr (rep n [false, true, false, true] blank) R) := by
  have h := start n R
  first | exact h | (rw [rot1] at h; exact h)

theorem p_carry (m : Nat) (L R : Tape) :
    steps (4 * m + 9) (arr L (app Dg.d.word (rep m W R))) =
      some (arr (rep m [false, true, false, true] (app [true, false, true, false, true] L)) R) := by
  have h := carry m L R
  first | exact h | (rw [rot1] at h; exact h)

theorem p_left_gap (k : Nat) (L R : Tape) :
    steps (6 * k) (ret (rep k [false, true, false, true] L) R) = some (ret L (rep k W R)) :=
  left_gap k L R

theorem p_left_d (L R : Tape) :
    steps 15 (ret (app [true, false, true, false, true] L) R) = some (ret L (app Dg.e.word R)) :=
  left_d L R

theorem p_left_end (R : Tape) :
    steps 6 (ret blank R) = some ⟨blank, app [false, false] (app W R), .A⟩ :=
  left_end R

/-! ## One pass: right to the digit that takes the increment, and back -/

theorem pass : ∀ (xs : List (Dg × Nat)) (δ : Nat) (ys : List (Dg × Nat)), bump xs = some (δ, ys) →
    ∀ L T : Tape, steps (cost xs) (arr L (enc xs T)) = some (ret L (rep δ W (enc ys T)))
  | [], _, _, h => by simp [bump] at h
  | (.d, h) :: xs, δ, ys, hb => by
    intro L T
    cases e : bump xs with
    | none => simp [bump, e] at hb
    | some p =>
      obtain ⟨δ', zs⟩ := p
      simp only [bump, e, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      have h1 := p_carry h L (enc xs T)
      have h2 := pass xs δ' zs e (rep h [false, true, false, true] (app [true, false, true, false, true] L)) T
      have h3 := p_left_gap h (app [true, false, true, false, true] L) (rep δ' W (enc zs T))
      have h4 := p_left_d L (rep h W (rep δ' W (enc zs T)))
      have h5 := steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4))
      have ee : enc ((Dg.e, h + δ') :: zs) T = app Dg.e.word (rep h W (rep δ' W (enc zs T))) := by
        simp only [enc, rep_add]
      rw [rep_zero, ee]
      exact steps_congr trans (by simp only [cost]; omega) h5
  | (.a, 0) :: _, _, _, h => by simp [bump] at h
  | (.b, 0) :: _, _, _, h => by simp [bump] at h
  | (.c, 0) :: _, _, _, h => by simp [bump] at h
  | (.e, 0) :: _, _, _, h => by simp [bump] at h
  | (.a, g + 1) :: xs, δ, ys, hb => by
    intro L T
    simp only [bump, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact bounce_a L (rep g W (enc xs T))
  | (.b, g + 1) :: xs, δ, ys, hb => by
    intro L T
    simp only [bump, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact bounce_b L (rep g W (enc xs T))
  | (.c, g + 1) :: xs, δ, ys, hb => by
    intro L T
    simp only [bump, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact bounce_c L (rep g W (enc xs T))
  | (.e, g + 1) :: xs, δ, ys, hb => by
    intro L T
    simp only [bump, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact bounce_e L (rep g W (enc xs T))

/-- **One visit is one increment.**  From a sample configuration whose increment `bump` is defined, the machine runs,
without halting, to the sample configuration of the incremented counter, in exactly
`10·g₀ + 11 + cost xs` steps. -/
theorem visit (g : Nat) (xs : List (Dg × Nat)) (T : Tape) (δ : Nat) (ys : List (Dg × Nat))
    (hb : bump xs = some (δ, ys)) :
    steps (10 * g + 11 + cost xs) (sample g xs T) = some (sample (g + 1 + δ) ys T) := by
  have h1 := p_start g (enc xs T)
  have h2 := pass xs δ ys hb (rep g [false, true, false, true] blank) T
  have h3 := p_left_gap g blank (rep δ W (enc ys T))
  have h4 := p_left_end (rep g W (rep δ W (enc ys T)))
  have h5 := steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4))
  have ee : rep (g + 1 + δ) W (enc ys T) = app W (rep g W (rep δ W (enc ys T))) := by
    rw [show g + 1 + δ = (g + δ) + 1 by omega, rep_succ, rep_add]
  unfold sample
  rw [ee]
  exact steps_congr trans (by omega) h5

/-- `visit` iterated: as long as `bump` stays defined, the counter keeps counting. -/
def run : Nat → Nat × List (Dg × Nat) → Option (Nat × List (Dg × Nat))
  | 0, s => some s
  | n + 1, (g, xs) =>
    match bump xs with
    | some (δ, ys) => run n (g + 1 + δ, ys)
    | none => none

theorem run_sound : ∀ (n : Nat) (g : Nat) (xs : List (Dg × Nat)) (g' : Nat) (ys : List (Dg × Nat)) (T : Tape),
    run n (g, xs) = some (g', ys) → ∃ k, steps k (sample g xs T) = some (sample g' ys T)
  | 0, g, xs, g', ys, T, h => by
    simp only [run, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨0, rfl⟩
  | n + 1, g, xs, g', ys, T, h => by
    cases e : bump xs with
    | none => simp [run, e] at h
    | some p =>
      obtain ⟨δ, zs⟩ := p
      simp only [run, e] at h
      obtain ⟨k, hk⟩ := run_sound n (g + 1 + δ) zs g' ys T h
      exact ⟨_, steps_seq trans (visit g xs T δ zs e) hk⟩

end H59221
