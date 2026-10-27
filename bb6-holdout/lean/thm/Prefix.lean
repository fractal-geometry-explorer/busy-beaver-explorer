import BB6.CleanTree

/-!
# The machine's run from blank tape to its clean tape of width 2³²

The mark model, run from the first round start (`roundStart [] 5`, 17 steps from blank tape), covers 1,204,297,272
rounds and arrives at the one-marker clean tape of width exactly 2³² = 4,294,967,296.  `prefix_ok` evaluates this
with `native_decide` (it trusts Lean's compiler as well as its kernel; with `--load-dynlib` and the BB6 modules
compiled to native code it takes a few minutes, interpreted about an hour), and `blank_prefix` turns it into a
statement about the machine through `blank_rounds`: from blank tape the machine reaches that round start, so it does
not halt on the way.
-/

namespace BB6

/-- The number of mark-model rounds from the first round start to the clean tape of width `prefixWidth`. -/
def prefixRounds : Nat := 1204297272

/-- 2³². -/
def prefixWidth : Nat := 4294967296

/-- The outcome is the one-marker clean tape of width `W`. -/
def oneMarkerAt (r : PR') (W : Nat) : Bool :=
  match r with
  | .newRound [⟨.M, p⟩] W' => p + 2 == W && W' == W
  | _ => false

theorem oneMarkerAt_eq {r : PR'} {W : Nat} (h : oneMarkerAt r W = true) : r = .newRound [⟨.M, W - 2⟩] W := by
  unfold oneMarkerAt at h
  split at h
  · rename_i p W'
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, rfl⟩ := h
    rw [show p = W' - 2 by omega]
  · cases h

theorem prefix_ok : oneMarkerAt (roundsZ 1000 prefixRounds [] 5) prefixWidth = true := by
  native_decide

/-- **From blank tape, the machine reaches the clean tape of width 2³²** (after 17 steps and 1,204,297,272 rounds of
the mark model), without halting on the way. -/
theorem blank_prefix :
    ∃ k, steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, prefixWidth - 2⟩] prefixWidth) := by
  have h := oneMarkerAt_eq prefix_ok
  obtain ⟨k, hk⟩ := blank_rounds 1000 prefixRounds (by rw [h]; intro h'; cases h')
  rw [h] at hk
  exact ⟨k, hk⟩

end BB6
