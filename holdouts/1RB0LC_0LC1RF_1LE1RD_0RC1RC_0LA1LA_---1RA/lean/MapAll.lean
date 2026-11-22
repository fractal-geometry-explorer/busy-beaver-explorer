import MapOdd
import Corner

/-!
# The whole A-event map in Lean

`nextAll` joins the three parts: `next` (even a, `Map.lean`), `nextOdd` (odd a ≥ 15, and odd a < 15 with b ≥ 30,
`MapOdd.lean`) and `nextCorner` (odd a < 15, b < 30, a checked table, `Corner.lean`).  `nextAll_sound`: wherever
it is defined, the machine goes from `Ev F a b` to the event it gives in exactly the steps it gives.
`nextAll_isSome`: it is defined at every event with a odd, and at every event with a even, a ≥ 2 and b ≥ 1 except
the halting events (a ≡ 0 mod 4, b = 1), which halt (`halt_event` in `HaltIff.lean`).  So the table of the README
is proved in full; the run from blank tape uses only its even-a part.
-/

namespace H13743

open TM

/-- The whole map. -/
def nextAll (F : Tag) (a b : Nat) : Option (Tag × Nat × Nat × Nat) :=
  (nextFull F a b).or (nextCorner F a b)

/-- **The whole map is sound.** -/
theorem nextAll_sound (F : Tag) (a b : Nat) (r : Tag × Nat × Nat × Nat) (h : nextAll F a b = some r) :
    steps r.2.2.2 (Ev F a b) = some (Ev r.1 r.2.1 r.2.2.1) := by
  unfold nextAll at h
  cases e : nextFull F a b with
  | some q => rw [e] at h; cases h; exact nextFull_sound F a b _ e
  | none => rw [e] at h; exact nextCorner_sound F a b r h

/-- **Where the whole map is defined**: every odd a, and every even a ≥ 2 with b ≥ 1 except the halting events. -/
theorem nextAll_isSome (F : Tag) (a b : Nat)
    (hd : a % 2 = 1 ∨ (a % 2 = 0 ∧ 2 ≤ a ∧ 1 ≤ b ∧ ¬(a % 4 = 0 ∧ b = 1))) : (nextAll F a b).isSome = true := by
  unfold nextAll
  by_cases hc : a % 2 = 1 ∧ a < 15 ∧ b < 30
  · have := nextCorner_isSome F a b hc.1 hc.2.1 hc.2.2
    cases nextFull F a b with
    | some q => rfl
    | none => exact this
  · have : (nextFull F a b).isSome = true := by
      apply nextFull_isSome
      rcases hd with h | h
      · exact Or.inr ⟨h, by omega⟩
      · exact Or.inl h
    cases e : nextFull F a b with
    | some q => rfl
    | none => rw [e] at this; cases this

end H13743
