import Macro

/-!
# A conserved counter for the macro machine

`py/callstack.py` reads the two-stack form of the macro machine as a recursive program: the right stack is a call
stack of frames `v<n>` (a loop that still has `n / 2` turns to run before it pushes `v`), the left stack is a data
stack.  The sum

    Φ = (sum of the left stack) + (sum of v + n over the frames, the last segment left out)

is a counter: interior steps keep it, and only the steps that reach an end of the tape change it.  In terms of the
macro configurations of `Macro.lean` (`n = g − 1`):

    Φ (F S ws mt)   = ΣS + Σ (m + g − 1)
    Φ (B S h ws mt) = ΣS + h + Σ (m + g − 1)
    Φ (Binf S)      = ΣS

`phi_interior`: a step from F that ends inside the word, and a step from B with a nonempty stack, keep Φ.
`phi_end`: a step from F that runs into the last segment adds 2 (the pass reaches blank tape) or 1 (two 1s side by
side next to the last segment).  `phi_bottom`: a step from B with an empty stack takes 1 off.  These cover every step
except the two from `Binf`, which only happen with blank tape ahead of B.  Kernel only.
-/

namespace BB6e

def ssum : List Nat → Int
  | [] => 0
  | s :: S => (s : Int) + ssum S

def wsum : List (Nat × Nat) → Int
  | [] => 0
  | (m, g) :: ws => (m : Int) + g - 1 + wsum ws

/-- The counter. -/
def phi : MC → Int
  | .F S ws _ => ssum S + wsum ws
  | .B S h ws _ => ssum S + h + wsum ws
  | .Binf S => ssum S

/-- A B configuration whose word is not empty: the pass that led to it ended inside the word. -/
def Interior : MC → Prop
  | .B _ _ (_ :: _) _ => True
  | _ => False

theorem fscan_phi (ws : List (Nat × Nat)) :
    ∀ (S : List Nat) (u mt : Nat) (M : MC), fscan S u ws mt = some M →
      (Interior M ∧ phi M = ssum S + u + wsum ws) ∨
      (∃ S' h mt', M = .B S' h [] mt' ∧ (phi M = ssum S + u + wsum ws + 2 ∨ phi M = ssum S + u + wsum ws + 1)) ∨
      (∃ S', M = .Binf S') := by
  induction ws with
  | nil =>
    intro S u mt M h
    simp only [fscan, Option.some.injEq] at h
    subst h
    right; left
    refine ⟨S, u + 2, mt, rfl, Or.inl ?_⟩
    simp only [phi, wsum]; push_cast; omega
  | cons p ws ih =>
    obtain ⟨m, g⟩ := p
    intro S u mt M h
    simp only [fscan] at h
    by_cases g1 : g = 1
    · subst g1
      simp only [ite_true] at h
      have := ih (u :: S) m mt M h
      simp only [ssum, wsum] at this ⊢
      push_cast at this ⊢
      rcases this with ⟨hi, e⟩ | ⟨S', hh, t', e1, e2⟩ | hb
      · left; exact ⟨hi, by omega⟩
      · right; left; exact ⟨S', hh, t', e1, by omega⟩
      · right; right; exact hb
    · simp only [g1, ite_false] at h
      by_cases g2 : 2 ≤ g
      · simp only [g2, ite_true, Option.some.injEq] at h
        subst h
        left
        refine ⟨trivial, ?_⟩
        simp only [phi, wsum]
        have : ((g - 2 : Nat) : Int) = (g : Int) - 2 := by omega
        rw [this]; omega
      · have g0 : g = 0 := by omega
        subst g0
        simp only [show ¬ (2 ≤ 0) by omega, ite_false] at h
        by_cases m0 : m = 0
        · simp [m0] at h
        simp only [m0, ite_false] at h
        cases ws with
        | nil =>
          by_cases t0 : mt = 0
          · simp only [t0, ite_true, Option.some.injEq] at h
            subst h
            right; right; exact ⟨_, rfl⟩
          · simp only [t0, ite_false, Option.some.injEq] at h
            subst h
            right; left
            refine ⟨_, _, _, rfl, Or.inr ?_⟩
            simp only [phi, ssum, wsum]; push_cast; omega
        | cons q ws' =>
          obtain ⟨m', g'⟩ := q
          by_cases z : m' = 0
          · simp [z] at h
          simp only [z, ite_false, Option.some.injEq] at h
          subst h
          left
          refine ⟨trivial, ?_⟩
          simp only [phi, ssum, wsum]
          have : ((m' - 1 : Nat) : Int) = (m' : Int) - 1 := by omega
          rw [this]; push_cast; omega

/-- **Interior steps keep the counter**: a pass from F that ends inside the word, and a step from B with a nonempty
stack. -/
theorem phi_interior (M M' : MC) (h : mstep M = some M') :
    (∀ S ws mt, M = .F S ws mt → Interior M' → phi M' = phi M) ∧
    (∀ j S hh ws mt, M = .B (j :: S) hh ws mt → phi M' = phi M) := by
  constructor
  · intro S ws mt e hi
    subst e
    rcases fscan_phi ws S 0 mt M' h with ⟨_, e⟩ | ⟨S', hh, t', e1, _⟩ | ⟨S', e1⟩
    · show phi M' = ssum S + wsum ws
      push_cast at e; omega
    · subst e1; exact absurd hi id
    · subst e1; exact absurd hi id
  · intro j S hh ws mt e
    subst e
    simp only [mstep] at h
    by_cases h0 : hh = 0
    · simp [h0] at h
    simp only [h0, ite_false, Option.some.injEq] at h
    subst h
    simp only [phi, ssum, wsum]
    have : ((hh - 1 : Nat) : Int) = (hh : Int) - 1 := by omega
    rw [this]; push_cast; omega

/-- **The tick**: a pass from F that runs into the last segment adds 2 (blank tape ahead) or 1 (two 1s side by side
next to the last segment). -/
theorem phi_end (S : List Nat) (ws : List (Nat × Nat)) (mt : Nat) (S' : List Nat) (hh mt' : Nat)
    (h : mstep (.F S ws mt) = some (.B S' hh [] mt')) :
    phi (.B S' hh [] mt') = phi (.F S ws mt) + 2 ∨ phi (.B S' hh [] mt') = phi (.F S ws mt) + 1 := by
  rcases fscan_phi ws S 0 mt _ h with ⟨hi, _⟩ | ⟨S'', h'', t'', e1, e2⟩ | ⟨_, e1⟩
  · exact absurd hi id
  · rw [e1] at e2 ⊢; simp only [phi] at e2 ⊢; push_cast at e2; omega
  · cases e1

/-- **The bottom**: B with an empty stack takes an entry −1 from below it, which takes 1 off the counter. -/
theorem phi_bottom (hh : Nat) (ws : List (Nat × Nat)) (mt : Nat) (M' : MC) (h : mstep (.B [] hh ws mt) = some M') :
    phi M' = phi (.B [] hh ws mt) - 1 := by
  simp only [mstep] at h
  by_cases h0 : hh = 0
  · simp [h0] at h
  simp only [h0, ite_false, Option.some.injEq] at h
  subst h
  simp only [phi, ssum, wsum]
  have : ((hh - 1 : Nat) : Int) = (hh : Int) - 1 := by omega
  rw [this]; push_cast; omega

end BB6e
