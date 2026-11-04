import Macro

/-!
# Blocks of at least 2, and a last block other than 1 and 4

A pass start `K ls n` (`Macro.lean`) has the blocks `ls` left of the last, nearest first, and the last block `n + 1`.
It halts on this pass if the last block is 1 (`K_zero_halts`) and on the next one if it is 4 (`kA0`).  `Good ls n`
says that neither happens and that no block to the left is shorter than 2.

`next_good`: the pass map of `Macro.lean` keeps `Good`.  So a run of covered passes (last block not a multiple of 3)
from a good pass start never halts, and a halt needs a pass with a last block that is a multiple of 3 (the recursive
case, not covered by `next`) to break `Good`.

`next_shrink`: when the last block is 1 mod 3, the last block plus 5 shrinks to exactly two thirds; when it is 2 mod 3
the last block grows by at least the block to its left.  These are the only two ways the covered passes move the
last block.
-/

namespace BB6c

/-- No block left of the last is shorter than 2, and the last block (`n + 1`) is neither 1 nor 4. -/
def Good (ls : List Nat) (n : Nat) : Prop := (∀ b ∈ ls, 2 ≤ b) ∧ n ≠ 0 ∧ n ≠ 3

theorem headD_good {ls : List Nat} (h : ∀ b ∈ ls, 2 ≤ b) : ls.headD 0 = 0 ∨ 2 ≤ ls.headD 0 := by
  cases ls with
  | nil => exact .inl rfl
  | cons a _ => exact .inr (h a (List.mem_cons_self ..))

theorem tail_good {ls : List Nat} (h : ∀ b ∈ ls, 2 ≤ b) : ∀ b ∈ ls.tail, 2 ≤ b :=
  fun b hb => h b (List.mem_of_mem_tail hb)

theorem cons_good {a : Nat} {ls : List Nat} (ha : 2 ≤ a) (h : ∀ b ∈ ls, 2 ≤ b) : ∀ b ∈ a :: ls, 2 ≤ b := by
  intro b hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact ha
  · exact h b hb

/-- **The covered passes keep `Good`.** -/
theorem next_good {ls ls' : List Nat} {n n' : Nat} (hg : Good ls n) (h : next ls n = some (ls', n')) :
    Good ls' n' := by
  obtain ⟨hb, h0, h3⟩ := hg
  have hx := headD_good hb
  have hd := headD_good (tail_good hb)
  dsimp only [next] at h
  split at h
  · exact absurd ‹n = 3› h3
  split at h
  · cases h; exact ⟨cons_good (by omega) (tail_good hb), by omega, by omega⟩
  split at h
  · cases h; exact ⟨cons_good (by omega) (tail_good hb), by omega, by omega⟩
  split at h
  · cases h; exact ⟨cons_good (by omega) (tail_good (tail_good hb)), by omega, by omega⟩
  split at h
  · cases h; exact ⟨cons_good (by omega) (tail_good (tail_good hb)), by omega, by omega⟩
  cases h

/-- `next` is defined on every pass start whose last block is not a multiple of 3 and not 1. -/
theorem next_isSome (ls : List Nat) {n : Nat} (h0 : n ≠ 0) (h2 : n % 3 ≠ 2) : (next ls n).isSome := by
  dsimp only [next]
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  omega

/-- **How the covered passes move the last block** (`n + 1`): if it is 1 mod 3, the last block plus 5 becomes two
thirds of what it was; if it is 2 mod 3, the new last block is the old block to its left plus at least 3. -/
theorem next_shrink {ls ls' : List Nat} {n n' : Nat} (h : next ls n = some (ls', n')) :
    (n % 3 = 0 ∧ 3 * (n' + 6) = 2 * (n + 6)) ∨ (n % 3 = 1 ∧ ls.headD 0 + 2 ≤ n' ∧ n' % 2 = (ls.headD 0) % 2) := by
  dsimp only [next] at h
  split at h
  · cases h; omega
  split at h
  · cases h; omega
  split at h
  · cases h; omega
  split at h
  · cases h; omega
  split at h
  · cases h; omega
  cases h

/-- `k` covered passes in a row (`none` if one of them is not covered). -/
def nextIter : Nat → List Nat → Nat → Option (List Nat × Nat)
  | 0, ls, n => some (ls, n)
  | k + 1, ls, n => (next ls n).bind fun p => nextIter k p.1 p.2

/-- Every pass start that covered passes reach from a good one is good, so none of them halts: a halt from a good
pass start needs a recursive pass (last block a multiple of 3) that breaks `Good`. -/
theorem nextIter_good : ∀ (k : Nat) {ls ls' : List Nat} {n n' : Nat}, Good ls n → nextIter k ls n = some (ls', n') →
    Good ls' n'
  | 0, _, _, _, _, hg, h => by cases h; exact hg
  | k + 1, ls, _, n, _, hg, h => by
    simp only [nextIter, Option.bind_eq_some_iff] at h
    obtain ⟨⟨l₁, n₁⟩, h₁, h₂⟩ := h
    exact nextIter_good k (next_good hg h₁) h₂

/-- Every covered pass is a real run of the machine (`next_sound`), so `nextIter` is too. -/
theorem nextIter_sound : ∀ (k : Nat) {ls ls' : List Nat} {n n' : Nat}, nextIter k ls n = some (ls', n') →
    Reaches (K ls n) (K ls' n')
  | 0, _, _, _, _, h => by cases h; exact ⟨0, rfl⟩
  | k + 1, ls, _, n, _, h => by
    simp only [nextIter, Option.bind_eq_some_iff] at h
    obtain ⟨⟨l₁, n₁⟩, h₁, h₂⟩ := h
    exact (next_sound h₁).trans (nextIter_sound k h₂)

end BB6c
