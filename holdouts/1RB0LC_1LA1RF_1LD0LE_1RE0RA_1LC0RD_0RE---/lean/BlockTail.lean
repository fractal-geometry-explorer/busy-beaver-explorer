import Movers

/-!
# The right sweep that ends on movers with one-pair gaps

`right_gen` (`Movers.lean`) needs the last swept mover to have a gap of at least two pairs, so that the head comes
out in state D.  When the swept block ends with one-pair gaps (the reservoir's words), the head crosses each of them
with `rm1_cells` or `fm1_cells` and comes out in state F.  `ones_F` and `ones_D` do any number `k + 1` of them at
once, and `ones_movers` reads what they leave as movers at rest again: `k` movers with one-pair gaps, below the
four cells `1 1 0 0` nearest the head.  `tail_D` and `tail_F` chain this behind `right_gen`.  This is the closed
form the one-stack simulator (`py/block_sim.py`) uses for the rm1 tail.  Checked by Lean's kernel.
-/

namespace H71372

open TM

/-- What `fm1_cells` leaves: `0 0 1 0 0 1 1` on the left of the head, written nearest first as `1 1 0 0 1 0 0`. -/
def g1 (L : Tape) : Tape :=
  cons true (cons true (cons false (cons false (cons true (cons false (cons false L))))))

/-- What `rm1_cells` leaves: the same with the far cell a 1. -/
def g1D (L : Tape) : Tape :=
  cons true (cons true (cons false (cons false (cons true (cons false (cons true L))))))

/-- `j` copies of `g1`. -/
def g1s : Nat → Tape → Tape
  | 0, L => L
  | j + 1, L => g1 (g1s j L)

theorem W1 (R : Tape) :
    W 1 R = cons false (cons true (cons false (cons true (cons true (cons false (cons true R)))))) := rfl

/-- In state F the head crosses `k` swept movers with one-pair gaps and stays in F. -/
theorem ones_F (k : Nat) (R : Tape) : ∀ L : Tape,
    steps (7 * k) ⟨L, swL (List.replicate k 1) R, .F⟩ = some ⟨g1s k L, R, .F⟩ := by
  induction k with
  | zero => intro L; rfl
  | succ k ih =>
    intro L
    have h1 : steps 7 ⟨L, swL (List.replicate (k + 1) 1) R, .F⟩ = some ⟨g1 L, swL (List.replicate k 1) R, .F⟩ := by
      simp only [List.replicate_succ, swL, W1]; exact fm1_cells L _
    have h2 := ih (g1 L)
    have e : g1s k (g1 L) = g1s (k + 1) L := by
      clear ih h1 h2
      induction k generalizing L with
      | zero => rfl
      | succ k ih' => simp only [g1s] at *; rw [ih' L]
    rw [e] at h2
    exact steps_congr trans (by omega) (steps_seq trans h1 h2)

/-- In state D the first one-pair mover sends the head into F (`rm1_cells`), and the rest keep it there. -/
theorem ones_D (k : Nat) (L R : Tape) :
    steps (7 * (k + 1)) ⟨L, swL (List.replicate (k + 1) 1) R, .D⟩ = some ⟨g1s k (g1D L), R, .F⟩ := by
  have h1 : steps 7 ⟨L, swL (List.replicate (k + 1) 1) R, .D⟩ = some ⟨g1D L, swL (List.replicate k 1) R, .F⟩ := by
    simp only [List.replicate_succ, swL, W1]; exact rm1_cells L _
  exact steps_congr trans (by omega) (steps_seq trans h1 (ones_F k R (g1D L)))

/-- What the one-pair movers leave is movers at rest again: `k` copies of `g1` in front of `1 1 0 0 Z` are the four
cells `1 1 0 0` in front of `k` movers with one-pair gaps in front of `Z`. -/
theorem ones_movers (k : Nat) (Z : Tape) :
    g1s k (cons true (cons true (cons false (cons false Z)))) =
      cons true (cons true (cons false (cons false (movers (List.replicate k 1) Z)))) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [g1s, ih, List.replicate_succ, movers]; rfl

/-- `g1` and `g1D` themselves start with `1 1 0 0`. -/
theorem g1_split (L : Tape) : g1 L = cons true (cons true (cons false (cons false
    (cons true (cons false (cons false L)))))) := rfl
theorem g1D_split (L : Tape) : g1D L = cons true (cons true (cons false (cons false
    (cons true (cons false (cons true L)))))) := rfl

/-- `k + 1` one-pair movers crossed from state D, read as movers: `1 1 0 0`, then `k` movers with one-pair gaps,
then `1 0 1` and the tape the head started from. -/
theorem ones_D_movers (k : Nat) (L R : Tape) :
    steps (7 * (k + 1)) ⟨L, swL (List.replicate (k + 1) 1) R, .D⟩ = some ⟨cons true (cons true (cons false
      (cons false (movers (List.replicate k 1) (cons true (cons false (cons true L))))))), R, .F⟩ := by
  rw [← ones_movers]; exact ones_D k L R

/-- The same from state F, with `1 0 0` at the far end. -/
theorem ones_F_movers (k : Nat) (L R : Tape) :
    steps (7 * (k + 1)) ⟨L, swL (List.replicate (k + 1) 1) R, .F⟩ = some ⟨cons true (cons true (cons false
      (cons false (movers (List.replicate k 1) (cons true (cons false (cons false L))))))), R, .F⟩ := by
  rw [← ones_movers]
  have h := ones_F (k + 1) R L
  have e : g1s (k + 1) L = g1s k (g1 L) := by
    clear h
    induction k generalizing L with
    | zero => rfl
    | succ k ih => simp only [g1s] at *; rw [← ih L]
  rw [e] at h; exact h

/-- **The right sweep over a block that ends with `k + 1` one-pair gaps**, entered in state D: `right_gen` over the
rest (the last of the rest at least two pairs), then the one-pair movers.  The head comes out in state F. -/
theorem tail_D (pre : List Nat) (hp : ∀ g ∈ pre, 1 ≤ g) (n k : Nat) (L R : Tape) :
    steps (rcost (pre ++ [n + 2]) + 7 * (k + 1))
        ⟨L, swL (pre ++ [n + 2] ++ List.replicate (k + 1) 1) R, .D⟩ =
      some ⟨cons true (cons true (cons false (cons false (movers (List.replicate k 1) (cons true (cons false
        (cons true (cons false (mv n (movers pre.reverse (cons true (cons false (cons true L))))))))))))), R, .F⟩ := by
  rw [swL_append]
  exact steps_seq trans ((right_gen pre hp n _ L).1) (ones_D_movers k _ R)

/-- The same entered in state F. -/
theorem tail_F (pre : List Nat) (hp : ∀ g ∈ pre, 1 ≤ g) (n k : Nat) (L R : Tape) :
    steps (rcost (pre ++ [n + 2]) + 7 * (k + 1))
        ⟨L, swL (pre ++ [n + 2] ++ List.replicate (k + 1) 1) R, .F⟩ =
      some ⟨cons true (cons true (cons false (cons false (movers (List.replicate k 1) (cons true (cons false
        (cons true (cons false (mv n (movers pre.reverse (cons true (cons false (cons false L))))))))))))), R, .F⟩ := by
  rw [swL_append]
  exact steps_seq trans ((right_gen pre hp n _ L).2) (ones_D_movers k _ R)

/-- Pairs pushed onto a mover at rest join its gap. -/
theorem mv_pairs (a g : Nat) (L : Tape) : rep a [true, false] (mv g L) = mv (a + g) L := by
  simp only [mv]; rw [rep_add]

end H71372
