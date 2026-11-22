import Machine
import MirrorClock

/-!
# From the mirror image back to 1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---

`MirrorClock.lean` proves the clock for the mirror image `H29824M` of the machine (L and R swapped).  Here: the
mirror of a configuration (`mir`: the head stays on its cell, the two sides swap) turns every run of the mirror
machine into a run of the machine (`steps_mir`), so the tick holds for the machine itself, at the right end of the
tape (`tick_right_end`).
-/

namespace H29824B

open TM

/-- The mirror image of a configuration, with the states renamed by `f`: the head stays on its cell, the left
side becomes the right side and back. -/
def mir {Q Q' : Type} (f : Q → Q') (c : Cfg Q) : Cfg Q' := ⟨tail c.r, cons (c.r 0) c.l, f c.st⟩

theorem cons_tail (s : Tape) : cons (s 0) (tail s) = s := by
  funext n; cases n <;> rfl

def flipD : Dir → Dir
  | .L => .R
  | .R => .L

/-- One step of a machine and its mirror image. -/
theorem step_mir {Q Q' : Type} (δ : Q → Bool → Option (Bool × Dir × Q)) (δ' : Q' → Bool → Option (Bool × Dir × Q'))
    (f : Q → Q') (hδ : ∀ q b, δ' (f q) b = (δ q b).map (fun t => (t.1, flipD t.2.1, f t.2.2))) (c : Cfg Q) :
    step δ' (mir f c) = (step δ c).map (mir f) := by
  obtain ⟨l, r, q⟩ := c
  rcases h : δ q (r 0) with _ | ⟨w, d, s⟩
  · simp [step, mir, hδ, h]
  · cases d
    · simp [step, mir, hδ, h, flipD]
      exact (cons_tail l).symm
    · simp [step, mir, hδ, h, flipD]

theorem steps_mir {Q Q' : Type} (δ : Q → Bool → Option (Bool × Dir × Q)) (δ' : Q' → Bool → Option (Bool × Dir × Q'))
    (f : Q → Q') (hδ : ∀ q b, δ' (f q) b = (δ q b).map (fun t => (t.1, flipD t.2.1, f t.2.2))) :
    ∀ (n : Nat) (c : Cfg Q), steps δ' n (mir f c) = (steps δ n c).map (mir f) := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ n ih =>
    intro c
    simp only [steps, step_mir δ δ' f hδ c]
    rcases step δ c with _ | c'
    · rfl
    · exact ih c'

/-- The states of the mirror machine as those of the machine. -/
def st : H29824M.St → H29824.St
  | .A => .A | .B => .B | .C => .C | .D => .D | .E => .E | .F => .F

theorem trans_mir : ∀ q b, H29824.trans (st q) b =
    (H29824M.trans q b).map (fun t => (t.1, flipD t.2.1, st t.2.2)) := by
  intro q b; cases q <;> cases b <;> rfl

/-- Every run of the mirror machine is, mirrored, a run of the machine. -/
theorem of_mirror {n : Nat} {c d : H29824M.Config} (h : H29824M.steps n c = some d) :
    H29824.steps n (mir st c) = some (mir st d) := by
  have := steps_mir H29824M.trans H29824.trans st trans_mir n c
  show steps H29824.trans n (mir st c) = _
  rw [this]
  show Option.map _ (H29824M.steps n c) = _
  rw [h]; rfl

/-- **The tick of the machine**, at the right end: the mirror image of `H29824M.tick_left_end`. -/
theorem tick_right_end (j : Nat) (W W' : Tape) (E : Nat) (h : H29824M.PChain (2 ^ j) W W' E) :
    H29824.steps (E + 12 * 2 ^ j - 2) (mir st ⟨blank, H29824M.J j W, .C⟩) =
      some (mir st ⟨blank, H29824M.J (j + 1) W', .C⟩) :=
  of_mirror (H29824M.tick_left_end j W W' E h)

/-- The tick of the machine for every tape to the right of the 2 0s it eats. -/
theorem tick (j : Nat) (W W' : Tape) (E : Nat) (h : H29824M.PChain (2 ^ j) W W' E) (L : Tape) :
    H29824.steps (E + 12 * 2 ^ j - 2)
      (mir st ⟨cons false (cons false L), H29824M.J j W, .C⟩) =
      some (mir st ⟨L, H29824M.J (j + 1) W', .C⟩) :=
  of_mirror (H29824M.tick j W W' E h L)

end H29824B
