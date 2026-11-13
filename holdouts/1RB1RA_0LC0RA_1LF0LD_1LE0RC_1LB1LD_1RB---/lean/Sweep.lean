import Rules

/-!
# 1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---: the left sweep on pairs of cells, and where a halt comes from

Written by hand.  The left sweep moves two cells at a time: state E reads the right cell of a pair, state D the left
cell.  A pair whose right cell is 1 is rewritten 01 -> 11 or 11 -> 10 and the sweep goes on (`e_pair`); `sweep` is
the same for any list of such pairs.  The other cases (right cell 0) are the single rules `e_bounce`, `e_z2_pass`,
`e_z2_bounce`, `e_end` and `e_prehalt` of `Rules.lean`.

`prehalt`: three steps before any halt the machine is in state E on a 0 with `1 0 0` to its left.
`nonhalting_of_no_1000`: if the run from blank tape never shows that pattern, the machine never halts.
-/

namespace H54596

open TM

/-- One regular pair: `c x E> 1` with x = 0 becomes `E> c 1 1` (2 steps), with x = 1 `E> c 1 0` (4 steps). -/
theorem e_pair (b c : Bool) (L R : Tape) :
    steps (if b then 4 else 2) ⟨cons b (cons c L), cons true R, .E⟩ =
      some ⟨L, cons c (cons true (cons (!b) R)), .E⟩ := by
  cases b <;> rfl

/-- The cells left of the first pair's left cell, nearest first: for each further pair its right cell (a 1) and its
left cell (`true` = 1). -/
def pairsL : List Bool → Tape → Tape
  | [], L => L
  | b :: bs, L => cons true (cons b (pairsL bs L))

/-- What the sweep leaves behind: the pair with left cell b becomes `1 (not b)`; later pairs are further left. -/
def pairsR : List Bool → Tape → Tape
  | [], R => R
  | b :: bs, R => pairsR bs (cons true (cons (!b) R))

/-- Steps of the sweep over the pairs. -/
def cost : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 4 else 2) + cost bs

/-- The regular left sweep over any number of pairs 01 / 11: every pair 01 becomes 11 and every pair 11 becomes 10. -/
theorem sweep (bs : List Bool) : ∀ (b c : Bool) (L R : Tape),
    steps (cost (b :: bs)) ⟨cons b (pairsL bs (cons c L)), cons true R, .E⟩ =
      some ⟨L, cons c (pairsR (b :: bs) R), .E⟩ := by
  induction bs with
  | nil => intro b c L R; simpa [cost, pairsL, pairsR] using e_pair b c L R
  | cons b' bs ih =>
    intro b c L R
    have h1 := e_pair b true (cons b' (pairsL bs (cons c L))) R
    have h2 := ih b' c L (cons true (cons (!b) R))
    exact steps_seq trans h1 h2

/-- The pattern a halt comes from: state E on a 0, with `1 0 0` to its left. -/
def Pre (c : Config) : Prop :=
  c.st = .E ∧ c.r 0 = false ∧ c.l 0 = false ∧ c.l 1 = false ∧ c.l 2 = true

theorem prehalt_aux (s : St) (a b d x y z u : Bool) (L R : Tape) (c : Config)
    (h : steps 3 ⟨cons a (cons b (cons d L)), cons x (cons y (cons z (cons u R))), s⟩ = some c)
    (hh : step c = none) : s = .E ∧ x = false ∧ a = false ∧ b = false ∧ d = true := by
  cases s <;> cases a <;> cases b <;> cases d <;> cases x <;> cases y <;> cases z <;> cases u <;>
    first
    | exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    | (cases h <;> cases hh)

/-- Three steps before a halt the machine shows the pattern `Pre`: the only way into the halting transition F1 is
E0 -> B0 -> C0 -> F, and F then reads the cell three to the left of where E stood. -/
theorem prehalt (c0 c : Config) (h : steps 3 c0 = some c) (hh : step c = none) : Pre c0 := by
  obtain ⟨l, r, s⟩ := c0
  have hl : l = cons (l 0) (cons (l 1) (cons (l 2) (tail (tail (tail l))))) := by
    funext n; rcases n with _ | _ | _ | n <;> rfl
  have hr : r = cons (r 0) (cons (r 1) (cons (r 2) (cons (r 3) (tail (tail (tail (tail r))))))) := by
    funext n; rcases n with _ | _ | _ | _ | n <;> rfl
  have h' : steps 3 ⟨cons (l 0) (cons (l 1) (cons (l 2) (tail (tail (tail l))))),
      cons (r 0) (cons (r 1) (cons (r 2) (cons (r 3) (tail (tail (tail (tail r))))))), s⟩ = some c := by
    rw [← hl, ← hr]; exact h
  exact prehalt_aux s _ _ _ _ _ _ _ _ _ c h' hh

theorem steps_split : ∀ (a b : Nat) (c c'' : Config), steps (a + b) c = some c'' →
    ∃ c', steps a c = some c' ∧ steps b c' = some c'' := by
  intro a
  induction a with
  | zero => intro b c c'' h; exact ⟨c, rfl, by simpa using h⟩
  | succ a ih =>
    intro b c c'' h
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [e] at h
    cases hs : step c with
    | none => simp [steps, TM.steps, hs] at h
    | some d =>
      have h0 : steps (a + b) d = some c'' := (steps_succ_of_step trans (a + b) hs).symm.trans h
      obtain ⟨c', h1, h2⟩ := ih b d c'' h0
      exact ⟨c', (steps_succ_of_step trans a hs).trans h1, h2⟩

/-- A halting run from blank tape passes through the pattern `Pre` (three steps before its end). -/
theorem pre_of_halts (H : HaltsFromBlank) : ∃ n c, steps n init = some c ∧ Pre c := by
  obtain ⟨n, c, h, hh⟩ := H
  by_cases hn : 3 ≤ n
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    obtain ⟨c0, h1, h2⟩ := steps_split k 3 init c h
    exact ⟨k, c0, h1, prehalt c0 c h2 hh⟩
  · have : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases this with rfl | rfl | rfl <;> (cases h <;> cases hh)

/-- If the run from blank tape never has state E on a 0 with `1 0 0` to its left, the machine never halts. -/
theorem nonhalting_of_no_1000 (h : ∀ n c, steps n init = some c → ¬ Pre c) : ¬ HaltsFromBlank := by
  intro H
  obtain ⟨n, c, hc, hp⟩ := pre_of_halts H
  exact h n c hc hp

/-- And the pattern does halt: from `1 0 0 E> 0` the machine halts after three steps. -/
theorem halts_of_1000 (L R : Tape) :
    ∃ c, steps 3 ⟨cons false (cons false (cons true L)), cons false R, .E⟩ = some c ∧ step c = none :=
  ⟨_, e_prehalt L R, rfl⟩

end H54596
