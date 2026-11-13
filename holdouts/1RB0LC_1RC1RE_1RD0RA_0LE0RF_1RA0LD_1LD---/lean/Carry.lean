import Sweep

/-!
# Sweeps that reach the left end, and the other phase of the right end

A sweep whose left pass meets no even digit reaches the leftmost block `1^r` (the tape left of it is blank).

* `r = 3` (`carry3_sweep`): `1^3` and the digits `(2k+1) (2k₂+1) …` become `1^3`, `2k+2` zeros, then
  `1 0^(2k₂) 1 …` as in a normal sweep; the tape grows three cells to the left.
* `r = 6j+9` (`carry9_sweep`): the leftmost block becomes `1^3` followed by `2j+3` zeros, the digits after it as in a
  normal sweep.

When `r` is even the machine does something else (a nested run of inner sweeps, see the README); that case is not
covered here.  It ends with the right end in its other phase, `0 1^4 B>0`, and the next sweep (`phase2_sweep`)
turns the last digit 1 into `2 0` and brings the right end back to `0 1 B>0`.

Everything here is checked by Lean's kernel.
-/

namespace H115779

open TM

theorem app_ones_six (j m : Nat) (T : Tape) :
    app (ones (6 * j + m)) T = rep j [true, true, true, true, true, true] (app (ones m) T) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 6 * (j + 1) + m = 6 + (6 * j + m) by omega, app_ones_add 6 (6 * j + m), ih]
    rfl

/-- **The carry at the left end, `1^3`.** -/
theorem carry3_sweep (k : Nat) (ks : List Nat) :
    steps (8 + lcost (k :: ks) + (8 * k + 37) + rcost ks + 4) (P (raw 3) (odds (k :: ks))) =
      some (P (raw 3) (stepD (List.replicate (2 * k + 2) 0) 0 ks)) := by
  have h0 := tail_left (enc (odds (k :: ks)) (raw 3))
  have h1 := left_pass (raw 3) (k :: ks) [] T0
  rw [List.nil_append] at h1
  have h2 : steps (8 * k + 37) ⟨enc [] (raw 3), cons false (modR (k :: ks) T0), .D⟩ =
      some ⟨app [true, true, true] (rep k [false, true, true, false, true, true]
        (app [false, true, true, false, true, true, false, true, true, true] blank)), modR ks T0, .A⟩ := by
    show steps (8 * k + 37) ⟨raw 3, cons false (cons false (cons false (rep (3 * k + 2) [true, false]
      (modR ks T0)))), .D⟩ = _
    rw [rep_3k2, rot3]
    exact carry3 k _
  have h3 := right_pass ks (rep k [false, true, true, false, true, true]
    (app [false, true, true, false, true, true, false, true, true, true] blank)) T0
  have h4 := tail_right (rpass ks (rep k [false, true, true, false, true, true]
    (app [false, true, true, false, true, true, false, true, true, true] blank)))
  rw [← tail_blank] at h4
  have e : rep k [false, true, true, false, true, true]
      (app [false, true, true, false, true, true, false, true, true, true] blank) =
      app (ones (3 * 0)) (cons false (enc (List.replicate (2 * k + 2) 0) (raw 3))) := by
    rw [show List.replicate (2 * k + 2) 0 = [] ++ List.replicate (2 * k + 2) 0 from rfl, enc_zeros,
      rep_add (2 * k) 2, rep_mul2]
    exact (rep_rotate k [false] [true, true, false, true, true, false] [false, true, true, false, true, true]
      rfl _).symm
  rw [e] at h2 h3 h4
  rw [← F_rpass (raw 3) ks (List.replicate (2 * k + 2) 0) 0]
  refine steps_congr trans ?_ (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4))))
  omega

/-- **The carry at the left end, `1^(6j+9)`.** -/
theorem carry9_sweep (j : Nat) (ks : List Nat) :
    steps (8 + lcost ks + (20 * j + 91) + rcost ks + 4) (P (raw (6 * j + 9)) (odds ks)) =
      some (P (raw 3) (stepD (List.replicate (2 * j + 3) 0) 0 ks)) := by
  have h0 := tail_left (enc (odds ks) (raw (6 * j + 9)))
  have h1 := left_pass (raw (6 * j + 9)) ks [] T0
  rw [List.nil_append] at h1
  have h2 : steps (20 * j + 91) ⟨enc [] (raw (6 * j + 9)), cons false (modR ks T0), .D⟩ =
      some ⟨app [true, true, true] (rep j [false, true, true, false, true, true]
        (app [false, true, true, false, true, true, false, true, true, false, true, true, true] blank)),
        modR ks T0, .A⟩ := by
    show steps (20 * j + 91) ⟨app (ones (6 * j + 9)) blank, cons false (modR ks T0), .D⟩ = _
    rw [app_ones_six, rot3]
    exact carry9 j _
  have h3 := right_pass ks (rep j [false, true, true, false, true, true]
    (app [false, true, true, false, true, true, false, true, true, false, true, true, true] blank)) T0
  have h4 := tail_right (rpass ks (rep j [false, true, true, false, true, true]
    (app [false, true, true, false, true, true, false, true, true, false, true, true, true] blank)))
  rw [← tail_blank] at h4
  have e : rep j [false, true, true, false, true, true]
      (app [false, true, true, false, true, true, false, true, true, false, true, true, true] blank) =
      app (ones (3 * 0)) (cons false (enc (List.replicate (2 * j + 3) 0) (raw 3))) := by
    rw [show List.replicate (2 * j + 3) 0 = [] ++ List.replicate (2 * j + 3) 0 from rfl, enc_zeros,
      rep_add (2 * j) 3, rep_mul2]
    exact (rep_rotate j [false] [true, true, false, true, true, false] [false, true, true, false, true, true]
      rfl _).symm
  rw [e] at h2 h3 h4
  rw [← F_rpass (raw 3) ks (List.replicate (2 * j + 3) 0) 0]
  refine steps_congr trans ?_ (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4))))
  omega

/-- The right end in its other phase: `L 0 1^(3d₁+2) … 0 1^(3dₘ+2) 0 1^4 B>0`. -/
def Q (L : Tape) (ds : List Nat) : Config := ⟨app [true, true, true, true] (cons false (enc ds L)), blank, .B⟩

/-- **The sweep from the other phase**: the last digit 1 becomes `2 0`. -/
theorem phase2_sweep (L : Tape) (ds : List Nat) :
    steps 25 (Q L (ds ++ [1])) = some (P L (ds ++ [2, 0])) := by
  unfold Q P
  rw [enc_snoc, show ds ++ [2, 0] = (ds ++ [2]) ++ [0] by simp, enc_snoc, enc_snoc]
  exact phase2 _

end H115779
