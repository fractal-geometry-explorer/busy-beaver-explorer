import BB6.SymSplit

/-!
# Checking stretches of rounds with the kernel

`PR'.isRound r ms W` tests that an outcome of the mark model is the round start `ms`, `W`, with Boolean comparisons
that Lean's kernel evaluates directly (`decide +kernel`).  `roundsZ_chain` puts two stretches of rounds together.
The generated files `thm/PrefixPieces*.lean` (`thm/gen_prefix.py`) check the run from blank tape in stretches this
way, and `thm/PrefixKernel.lean` chains them.
-/

namespace BB6

/-- Equal mark lists, compared mark by mark. -/
def marksEqB : List Mark → List Mark → Bool
  | [], [] => true
  | a :: as, b :: bs => a.t == b.t && a.p == b.p && marksEqB as bs
  | _, _ => false

theorem marksEqB_eq : ∀ {as bs : List Mark}, marksEqB as bs = true → as = bs
  | [], [], _ => rfl
  | ⟨t, p⟩ :: as, ⟨t', p'⟩ :: bs, h => by
    simp only [marksEqB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    rw [marksEqB_eq h]
  | [], _ :: _, h => by simp [marksEqB] at h
  | _ :: _, [], h => by simp [marksEqB] at h

/-- The outcome is the round start with marks `ms` and width `W`. -/
def PR'.isRound : PR' → List Mark → Nat → Bool
  | .newRound ms W, ms', W' => marksEqB ms ms' && W == W'
  | _, _, _ => false

theorem PR'.isRound_eq {r : PR'} {ms : List Mark} {W : Nat} (h : r.isRound ms W = true) : r = .newRound ms W := by
  cases r with
  | newRound ms₀ W₀ =>
    simp only [PR'.isRound, Bool.and_eq_true, beq_iff_eq] at h
    rw [marksEqB_eq h.1, h.2]
  | _ => simp [PR'.isRound] at h

/-- Two stretches of rounds, one after the other. -/
theorem roundsZ_chain {fuel a b : Nat} {ms : List Mark} {W : Nat} {ms' : List Mark} {W' : Nat} {ms'' : List Mark}
    {W'' : Nat} (h₁ : roundsZ fuel a ms W = .newRound ms' W') (h₂ : roundsZ fuel b ms' W' = .newRound ms'' W'') :
    roundsZ fuel (a + b) ms W = .newRound ms'' W'' :=
  (Sym.roundsZ_add fuel a b ms W ms' W' h₁).trans h₂

end BB6
