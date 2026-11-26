import Machine
import Blank
import Halt

/-!
# No two 0s in a row left of the head, so a halt can only happen at the left end

Written by hand.  Kernel only.

`NoGap t` says the stream `t` never has `0 0` followed by a `1`: once two 0s in a row appear,
everything further out is blank.  For the left stream this says that the tape left of the head,
with its leading blanks removed, contains no `00`.

Why it holds: a right move puts the written cell in front of the left stream, and the only
transition that writes 0 and moves right is B0 → 0RC.  B is entered only by A0 → 1RB and C1 → 1RB, which write 1 and move right,
so in state B the cell left of the head is 1 and the new 0 never sits next to another 0.  A left move
only drops the nearest cell.  The run starts in A on blank tape, so the invariant holds at the start.

This is the proof of `holdouts/1RB1RF_1RC1LC_1LD0LE_---1LE_1RF0LB_0RA1RE/lean/LeftEnd.lean` (the same table with
the states renamed, started in another state), with the names changed.

With `halt_needs_pattern` (A reading 1 with `0 0 1` on its left) this gives `halt_at_left_end`:
a halt from blank tape needs A to read a 1 whose left neighbour is the leftmost 1 of the tape.
-/

namespace H132972

open TM

/-- No `0 0` with something nonblank further out. -/
def NoGap (t : Tape) : Prop := ∀ i, t i = false → t (i + 1) = false → t (i + 2) = false

/-- The invariant of the run from blank tape. -/
def Inv (c : Config) : Prop := NoGap c.l ∧ (c.st = .B → c.l 0 = true)

theorem nogap_zeros {t : Tape} (h : NoGap t) {i : Nat} (h0 : t i = false) (h1 : t (i + 1) = false) :
    ∀ k, t (i + k) = false := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    match k, ih with
    | 0, _ => simpa using h0
    | 1, _ => simpa using h1
    | k + 2, ih =>
      have a := ih k (by omega)
      have b := ih (k + 1) (by omega)
      have := h (i + k) a (by simpa [Nat.add_assoc] using b)
      simpa [Nat.add_assoc] using this

theorem nogap_tail {t : Tape} (h : NoGap t) : NoGap (tail t) := fun i a b => h (i + 1) a b

theorem nogap_cons_true {t : Tape} (h : NoGap t) : NoGap (cons true t) := by
  intro i a b
  cases i with
  | zero => simp at a
  | succ i => exact h i a b

theorem nogap_cons_false {t : Tape} (h : NoGap t) (h0 : t 0 = true) : NoGap (cons false t) := by
  intro i a b
  cases i with
  | zero => simp [h0] at b
  | succ i => exact h i a b

theorem inv_step {c c' : Config} (hc : Inv c) (hs : step c = some c') : Inv c' := by
  obtain ⟨l, r, s⟩ := c
  obtain ⟨hg, hf⟩ := hc
  cases s <;> cases e : r 0 <;> simp [step, TM.step, trans, e] at hs <;> subst hs <;>
    first
    | exact ⟨nogap_cons_true hg, fun _ => rfl⟩
    | exact ⟨nogap_tail hg, fun h => by cases h⟩
    | exact ⟨nogap_cons_false hg (hf rfl), fun h => by cases h⟩

theorem inv_steps : ∀ (n : Nat) {c c' : Config}, Inv c → steps n c = some c' → Inv c'
  | 0, c, c', hc, h => by
    simp [steps, TM.steps] at h; subst h; exact hc
  | n + 1, c, c', hc, h => by
    cases hs : step c with
    | none => simp [steps, TM.steps, hs] at h
    | some d =>
      rw [show steps (n + 1) c = steps n d from TM.steps_succ_of_step trans n hs] at h
      exact inv_steps n (inv_step hc hs) h

theorem inv_init : Inv init := ⟨fun _ _ _ => rfl, fun h => by cases h⟩

/-- Every configuration of the run from blank tape satisfies the invariant. -/
theorem reachable_nogap {n : Nat} {c : Config} (h : steps n init = some c) : NoGap c.l :=
  (inv_steps n inv_init h).1

/-- A halt from blank tape needs A reading 1 next to the leftmost 1 of the tape: the cell left of
the head is 1 and every cell beyond it is blank. -/
theorem halt_at_left_end (h : HaltsFromBlank) :
    ∃ n c, steps n init = some c ∧ c.st = .A ∧ c.r 0 = true ∧ c.l 0 = true ∧
      ∀ k, c.l (k + 1) = false := by
  obtain ⟨n, c, hc, hE, hr, hl0, hl1, hl2⟩ := halt_needs_pattern h
  refine ⟨n, c, hc, hE, hr, hl0, ?_⟩
  intro k
  have := nogap_zeros (reachable_nogap hc) hl1 hl2 k
  simpa [Nat.add_comm] using this

end H132972
