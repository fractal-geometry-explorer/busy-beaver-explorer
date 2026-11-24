import FamilyRule
import StepPasses

/-!
# Single steps of the walk, for every length

`py/map.py` writes the rebuild as a walk over the digits of the up-counter N.  On the tape the walk moves between
*clean configurations*: state D on a header (`0110101` or `0110111`), `00` on its left, the unread digits of N as
5-cell words above a short suffix, and the down-counter V as pairs on the right.  One step reads a block of the
lowest unread digits and goes to the next clean configuration, through local passes (`StepPasses.lean`, written by
`py/gen_steps.py`) and phases of ticks (`Phase.lean`).  The steps that read a run of ones run phases of
2^(length) ticks, so each needs the phase lemma and the value of V along the way.

`step1` is the first such step: suffix `1001`, header `0110111`, digits (top to bottom) `0 0 1^(2t+3)`, for every
t ≥ 1 and every rest of the counter and every V with at least 2^(2t) as its value.  It is the template for the
others (the census of step families is in the project notes; generating them is the next task).
-/
set_option linter.unusedSimpArgs false

namespace H49767
open TM

local notation "rf" => List.replicate

theorem s1_stage0 (t : Nat) (L : Tape) (v0 : List Bool) (R0 : Tape) :
    Reach ⟨cons false (cons false (app [true, false, false, true] (encU (rf (2 * t + 3) true) (cons false L)))),
            app hdr1 (encV v0 R0), .D⟩
      (tcfg hdr0 (true :: rf (2 * t + 1) false) ([false, true, false, false] ++ v0) (cons false (cons true L)) R0) := by
  have h := s1p0 t L (cons true (cons true (cons true (encV v0 R0))))
  refine reach_congr h ?_ ?_
  · simp only [encU_replicate, dU, hdr1]
    rw [rep_3_2m]
    simp only [app, rep_succ, List.cons_append, List.nil_append]
  · simp only [tcfg, encU, encU_replicate, encV_append, encV, dU, dV, hdr0, app]
    rw [rep_succ, rep_two_mul]
    simp only [app, rep_succ, List.cons_append, List.nil_append]


theorem s1_stage1 (t : Nat) (L : Tape) (w : List Bool) (R0 : Tape) :
    Reach (tcfg hdr0 (rf (2 * t + 2) true) ([false, false, true] ++ w) (cons false (cons true L)) R0)
      (tcfg hdr0 (rf (2 * t + 2) false) ([true, true, false] ++ w) (cons true (cons true L)) R0) := by
  have h := s1p1 t (cons true L) (cons true (encV w R0))
  refine reach_congr h ?_ ?_
  · simp only [tcfg, encU_replicate, encV_append, encV, dU, dV, hdr0]
    rw [show 2 * t + 2 = 2 * (t + 1) by omega, rep_two_mul]
    simp only [app, rep_succ, List.cons_append, List.nil_append]
  · simp only [tcfg, encU_replicate, encV_append, encV, dU, dV, hdr0]
    rw [show 2 * t + 2 = 2 * (t + 1) by omega, rep_two_mul]
    simp only [app, rep_succ, List.cons_append, List.nil_append]

theorem rep01_comm (n : Nat) (X : Tape) :
    cons false (cons true (rep n [false, true, false, true, false, true, false, true, false, true] X)) =
      rep n [false, true, false, true, false, true, false, true, false, true] (cons false (cons true X)) :=
  rep_rotate n [false, true] [false, true, false, true, false, true, false, true, false, true]
    [false, true, false, true, false, true, false, true, false, true] rfl X

theorem s1_stage2 (t : Nat) (Lx : Tape) (v : List Bool) (R0 : Tape) :
    Reach (tcfg hdr0 (rf (2 * t + 2) true) v (cons true (cons true (app [false, false, false, false] Lx))) R0)
      ⟨Lx, app hdr1 (encV (rf (5 * t + 7) true ++ false :: true :: v) R0), .D⟩ := by
  have h := s1p2 t Lx (cons true (cons false (cons true (encV v R0))))
  refine reach_congr h ?_ ?_
  · simp only [tcfg, encU_replicate, dU, hdr0]
    have e : rep (2 * t + 2) [true, false, false, false, false] (cons true (cons true (app [false, false, false, false] Lx))) =
        app [true] (rep (2 * t + 2) [false, false, false, false, true] (cons true (app [false, false, false, false] Lx))) := by
      rw [rep_rotate (2 * t + 2) [true] [false, false, false, false, true] [true, false, false, false, false] rfl]; rfl
    rw [e, show 2 * t + 2 = 2 * (t + 1) by omega, rep_two_mul]
    simp only [app, rep_succ, List.cons_append, List.nil_append]
  · simp only [encV_append, encV_replicate, encV, dV, hdr1]
    rw [show 5 * t + 7 = (5 * (t + 1)) + 2 by omega, rep_add (5 * (t + 1)) 2, rep_five_mul _ _ (t + 1)]
    simp only [rep01_comm, rep_succ, rep_zero, app, List.cons_append, List.nil_append]

/-! ## Bit lists of a given value -/

/-- The `L` lowest bits of `n`, least significant first. -/
def bitsOf : Nat → Nat → List Bool
  | 0, _ => []
  | L + 1, n => (n % 2 == 1) :: bitsOf L (n / 2)

theorem length_bitsOf : ∀ L n, (bitsOf L n).length = L
  | 0, _ => rfl
  | L + 1, n => by simp [bitsOf, length_bitsOf L]

theorem val_bitsOf : ∀ L n, n < 2 ^ L → val (bitsOf L n) = n
  | 0, n, h => by simp at h; simp [bitsOf, val, h]
  | L + 1, n, h => by
    have h2 : n < 2 ^ L * 2 := by rw [← Nat.pow_succ]; exact h
    have h' : n / 2 < 2 ^ L := by omega
    have ih := val_bitsOf L (n / 2) h'
    simp only [bitsOf, val, ih]
    by_cases hn : n % 2 = 1 <;> simp [hn] <;> omega

theorem encU_append : ∀ (a b : List Bool) (L : Tape), encU (a ++ b) L = encU a (encU b L)
  | [], _, _ => rfl
  | x :: a, b, L => by simp [encU, encU_append a b L]

/-! ## The whole step -/

/-- **One step of the walk**, state `1001` with header `0110111`, digits (top to bottom) `0 0 1^(2t+3)`, t = r + 1:
the rest X of the counter is untouched, the new state is `000` with header `0110111`, and the down-counter v0
becomes `1^(5t+7) 0 1 v2` with v2 = 16 v0 + 4 − 2^(2t+3) (5t + 13 more digits). -/
theorem step1 (r : Nat) (X : List Bool) (Ltop : Tape) (v0 : List Bool) (R0 : Tape) (hv : 2 ^ (2 * r + 2) ≤ val v0) :
    Reach ⟨cons false (cons false (app [true, false, false, true]
              (encU (rf (2 * (r + 1) + 3) true ++ false :: false :: X) Ltop))), app hdr1 (encV v0 R0), .D⟩
      ⟨cons false (cons false (app [false, false, false] (encU X Ltop))),
        app hdr1 (encV (rf (5 * (r + 1) + 7) true ++ false :: true ::
          bitsOf (v0.length + 4) (16 * val v0 + 4 - 2 ^ (2 * (r + 1) + 3))) R0), .D⟩ := by
  generalize ht : r + 1 = t
  have P2 : 2 ^ (2 * r + 2) = 2 * 2 ^ (2 * r + 1) := by rw [Nat.pow_succ]; omega
  have P8 : 2 ^ (2 * t + 2) = 8 * 2 ^ (2 * r + 1) := by
    rw [← ht, show 2 * (r + 1) + 2 = (2 * r + 1) + 3 by omega, Nat.pow_add]; omega
  have P16 : 2 ^ (2 * t + 3) = 16 * 2 ^ (2 * r + 1) := by
    rw [← ht, show 2 * (r + 1) + 3 = (2 * r + 1) + 4 by omega, Nat.pow_add]; omega
  generalize hP : 2 ^ (2 * r + 1) = P at P2 P8 P16
  have hvl := val_lt v0
  generalize hL : v0.length = n at hvl
  have hn : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
  have hn4 : 2 ^ (n + 4) = 16 * 2 ^ n := by rw [Nat.pow_add]; omega
  -- the two lists of the down-counter after the phases
  let w := bitsOf (n + 1) (2 * val v0 - P)
  have hw : val w = 2 * val v0 - P := val_bitsOf _ _ (by omega)
  have lw : w.length = n + 1 := length_bitsOf _ _
  let v2 := bitsOf (n + 4) (16 * val v0 + 4 - 16 * P)
  have hv2 : val v2 = 16 * val v0 + 4 - 16 * P := val_bitsOf _ _ (by omega)
  have lv2 : v2.length = n + 4 := length_bitsOf _ _
  have o1 := val_ones (2 * t + 2)
  rw [P8] at o1
  have lu1 : (true :: rf (2 * t + 1) false).length = 2 * t + 2 := by simp
  have lu2 : (rf (2 * t + 2) false).length = 2 * t + 2 := by simp
  have L0 : encU (rf (2 * t + 3) true ++ false :: false :: X) Ltop =
      encU (rf (2 * t + 3) true) (cons false (app [false, false, false, false] (app [false, false, false, false, false] (encU X Ltop)))) := by
    rw [encU_append]; rfl
  rw [L0, P16]
  refine (s1_stage0 t _ v0 R0).trans ?_
  refine (phase_exact hdr0 (Or.inl rfl) _ _ (rf (2 * t + 2) true) ([false, false, true] ++ w) _ R0 (8 * P - 2)
    ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
  · simp [val_append, val, hL]; omega
  · rw [lu1, P8]; simp [val, val_replicate_false]; omega
  · simp
  · simp [lw, hL]
  · simp [val, val_replicate_false]; omega
  · simp [val_append, val, hw, hL]; omega
  refine (s1_stage1 t _ w R0).trans ?_
  refine (phase_exact hdr0 (Or.inl rfl) _ _ (rf (2 * t + 2) true) v2 _ R0 (8 * P - 1)
    ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
  · simp [val_append, val, hw, lw]; omega
  · rw [lu2, P8]; simp [val_replicate_false]; omega
  · simp
  · simp [lv2, lw]
  · simp [val_replicate_false]; omega
  · simp [val_append, val, hw, hv2, lw]; omega
  exact s1_stage2 t (app [false, false, false, false, false] (encU X Ltop)) v2 R0

end H49767
