import Top
import Ends

/-!
# How a reset of 1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE ends

A reset from `Qc 2 y` runs ternary rounds `L(a, k + 2a + 1) → L(3a + 2, k)` (`Top.lean`) until the right block has
fewer than `2a + 1` pairs. Then one of five things happens (the rules in `Ends.lean`), and Lean follows every
case for all sizes:

* the reset is **over** and the bouncer `Q(x', y')` starts again: from `L(a, 1)`, from a round step `S(p, m, 0)`,
  or from `S(0, m, 1)`;
* or the run reaches a **nested start** `N(P, M)` = `1^P 0 (10)^M 1^4 0 A>`: a small tank to the right of the
  pairs, from `L(a, 0)` or `S(p + 2, m, 1)`. From there the same kind of rounds run again inside, with the pairs
  `(10)^M` and the 1s `1^P` as the budget (the nested rounds of the README); that part is not in Lean.

Main results: `reset_end` (`Qc 2 y` reaches `(resetEnd y).cfg` for every `y ≥ 2`, with `resetEnd` an explicit
function), `reset_step` (when the reset is over, `Qc 2 y` reaches the next reset `Qc 2 (resetMap y)`), and
`blank_to_nested`: blank tape reaches the nested start `N(35, 26)` through the resets `y = 4, 38`.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace H95029

open TM

/-- `1^P 0 (10)^M 1^4 0 A>` (blank tape on both sides): a nested start. -/
def Nc (P M : Nat) : Config :=
  ⟨cons false (rep 4 [true] (rep M [false, true] (cons false (rep P [true] blank)))), blank, .A⟩

/-- Where a reset ends: the bouncer `Q(x, y)` or a nested start `N(P, M)`. -/
inductive Out where
  | q (x y : Nat)
  | n (P M : Nat)
  deriving DecidableEq, Repr

def Out.cfg : Out → Config
  | .q x y => Qc x y
  | .n P M => Nc P M

abbrev R1 : Tape := cons true blank

/-! ## The five ends, on the configurations of `Top.lean` -/

theorem end_s0 (p m : Nat) : Reaches (Sc p m 0 R1) (Qc (p + 1) (m + 2)) := by
  have h := e_s0 m p
  rw [cons_false_blank] at h
  exact Reaches.of h

theorem end_s1 (p m : Nat) : Reaches (Sc (p + 2) m 1 R1) (Nc (p + 1) (m + 4)) := by
  have h := e_s1 m p
  have e : cons false (cons true (cons false (cons true (cons false (cons true (rep m [false, true] (cons false
      (cons true (cons false (cons true (rep p [true] blank)))))))))))
      = rep (m + 4) [false, true] (cons false (rep (p + 1) [true] blank)) := by
    show rep 3 [false, true] (rep m [false, true] (rep 1 [false, true] (cons false (rep (p + 1) [true] blank)))) = _
    rw [← rep_add, ← rep_add, show 3 + m + 1 = m + 4 by omega]
  rw [e] at h
  exact Reaches.of h

theorem end_s01 (m : Nat) : Reaches (Sc 0 m 1 R1) (Qc (2 * m + 9) 0) := by
  have h := e_s01 m
  rw [cons_false_blank, n_pair] at h
  have e : cons true (cons true (cons true (cons true (rep (2 * m) [true] (cons true (cons true (cons true (cons true
      (cons true blank))))))))) = rep (2 * m + 9) [true] blank := by
    show rep 4 [true] (rep (2 * m) [true] (rep 5 [true] blank)) = _
    rw [← rep_add, ← rep_add, show 4 + 2 * m + 5 = 2 * m + 9 by omega]
  rw [e] at h
  exact Reaches.of h

theorem end_l0 (b : Nat) : Reaches (Lc (b + 1) 0 R1) (Nc (2 * b + 1) 2) := by
  have h := e_l0 b
  rw [n_pair] at h
  exact Reaches.of h

theorem end_l1 (b : Nat) : Reaches (Lc (b + 1) 1 R1) (Qc (2 * b + 1) 3) := by
  have h := e_l1 b
  rw [cons_false_blank, n_pair] at h
  exact Reaches.of h

/-! ## The end of the rounds -/

/-- The end of a reset from `L(a, K)` with `K < 2a + 1` (fewer right pairs than a full round needs). -/
def finish (a K : Nat) : Out :=
  if K = 0 then .n (2 * a - 1) 2
  else if K = 1 then .q (2 * a - 1) 3
  else if (K - 1) % 2 = 0 then .q (2 * a - 2 - 2 * ((K - 1) / 2) + 1) (1 + 3 * ((K - 1) / 2) + 2)
  else if 2 ≤ 2 * a - 2 - 2 * ((K - 1) / 2) then .n (2 * a - 2 - 2 * ((K - 1) / 2) - 1) (1 + 3 * ((K - 1) / 2) + 4)
  else .q (2 * (1 + 3 * ((K - 1) / 2)) + 9) 0

theorem finish_sem (a K : Nat) (ha : 2 ≤ a) (hK : K < 2 * a + 1) : Reaches (Lc a K R1) (finish a K).cfg := by
  unfold finish
  by_cases h0 : K = 0
  · subst h0; rw [if_pos rfl]
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [show 2 * (b + 1) - 1 = 2 * b + 1 by omega]; exact end_l0 b
  rw [if_neg h0]
  by_cases h1 : K = 1
  · subst h1; rw [if_pos rfl]
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [show 2 * (b + 1) - 1 = 2 * b + 1 by omega]; exact end_l1 b
  rw [if_neg h1]
  -- K ≥ 2: the round starts, then j round steps
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 2 := ⟨K - 2, by omega⟩
  have hs := Reaches.of (l_to_s a' k R1)
  have hj : ∀ p j r, 2 * a' + 2 = p + 2 * j → k + 1 = r + 2 * j → Reaches (Lc (a' + 2) (k + 2) R1) (Sc p (1 + 3 * j) r R1) := by
    intro p j r hp hr
    have h2 := s_iter j R1 p 1 r
    rw [← hp, ← hr] at h2
    exact hs.tr h2
  rw [show k + 2 - 1 = k + 1 by omega]
  by_cases hr : (k + 1) % 2 = 0
  · rw [if_pos hr]
    exact (hj _ ((k + 1) / 2) 0 (by omega) (by omega)).tr (end_s0 _ _)
  rw [if_neg hr]
  by_cases hp : 2 ≤ 2 * (a' + 2) - 2 - 2 * ((k + 1) / 2)
  · rw [if_pos hp]
    have h := (hj (2 * (a' + 2) - 2 - 2 * ((k + 1) / 2) - 2 + 2) ((k + 1) / 2) 1 (by omega) (by omega)).tr (end_s1 _ _)
    rw [show 2 * (a' + 2) - 2 - 2 * ((k + 1) / 2) - 2 + 1 = 2 * (a' + 2) - 2 - 2 * ((k + 1) / 2) - 1 by omega] at h
    exact h
  · rw [if_neg hp]
    exact (hj 0 ((k + 1) / 2) 1 (by omega) (by omega)).tr (end_s01 _)

/-- The rounds from `L(a, K)`, then their end (`f` is fuel: `K ≤ f` is enough, each round uses at least 5 pairs). -/
def roundsTo : Nat → Nat → Nat → Out
  | 0, a, K => finish a K
  | f + 1, a, K => if 2 * a + 1 ≤ K then roundsTo f (3 * a + 2) (K - (2 * a + 1)) else finish a K

theorem roundsTo_sem (f : Nat) : ∀ a K, 2 ≤ a → K ≤ f → Reaches (Lc a K R1) (roundsTo f a K).cfg := by
  induction f with
  | zero => intro a K ha hK; exact finish_sem a K ha (by omega)
  | succ f ih =>
    intro a K ha hK
    simp only [roundsTo]
    split
    · next h =>
      have h1 := round a (K - (2 * a + 1)) R1 ha
      rw [show K - (2 * a + 1) + 2 * a + 1 = K by omega] at h1
      exact h1.tr (ih _ _ (by omega) (by omega))
    · next h => exact finish_sem a K ha (by omega)

/-- Where the reset from `Qc 2 y` ends. -/
def resetEnd (y : Nat) : Out := roundsTo y 2 y

/-- **The end of every reset, for every `y ≥ 2`.** -/
theorem reset_end (y : Nat) (hy : 2 ≤ y) : Reaches (Qc 2 y) (resetEnd y).cfg := by
  obtain ⟨y', rfl⟩ : ∃ y', y = y' + 2 := ⟨y - 2, by omega⟩
  exact (Reaches.of (q_two y')).tr (roundsTo_sem _ 2 _ (by omega) (Nat.le_refl _))

/-- The next reset, when the reset from `Qc 2 y` is over (no nesting): the bouncer runs to `Qc 2 (next2 x y')`. -/
def resetMap (y : Nat) : Option Nat :=
  match resetEnd y with
  | .q x y' => some (next2 x y')
  | .n _ _ => none

theorem out_q_pos (a K x y : Nat) (ha : 2 ≤ a) (h : finish a K = .q x y) : 1 ≤ x := by
  unfold finish at h
  split at h
  · cases h
  split at h
  · cases h; omega
  split at h
  · cases h; omega
  split at h
  · cases h
  · cases h; omega

theorem roundsTo_q_pos (f : Nat) : ∀ a K x y, 2 ≤ a → roundsTo f a K = .q x y → 1 ≤ x := by
  induction f with
  | zero => intro a K x y ha h; exact out_q_pos a K x y ha h
  | succ f ih =>
    intro a K x y ha h
    simp only [roundsTo] at h
    split at h
    · exact ih _ _ x y (by omega) h
    · exact out_q_pos a K x y ha h

/-- **A reset that is over leads to the next reset.** -/
theorem reset_step (y y' : Nat) (hy : 2 ≤ y) (h : resetMap y = some y') : Reaches (Qc 2 y) (Qc 2 y') := by
  unfold resetMap at h
  have he := reset_end y hy
  cases ho : resetEnd y with
  | q x z =>
    rw [ho] at h he
    cases h
    exact he.tr (q_to_two x z (roundsTo_q_pos y 2 y x z (by omega) ho))
  | n P M => rw [ho] at h; cases h

/-! ## From blank tape -/

/-- Blank tape reaches the resets `y = 4` and `y = 38`, and the reset from 38 ends in the nested start
`N(35, 26)` = `1^35 0 (10)^26 1^4 0 A>`. -/
theorem blank_to_nested : Reaches init (Nc 35 26) := by
  have h1 := reset_step 4 38 (by omega) (by decide)
  have h2 := reset_end 38 (by omega)
  rw [show resetEnd 38 = .n 35 26 by decide] at h2
  exact blank_to_two.tr (h1.tr h2)

end H95029
