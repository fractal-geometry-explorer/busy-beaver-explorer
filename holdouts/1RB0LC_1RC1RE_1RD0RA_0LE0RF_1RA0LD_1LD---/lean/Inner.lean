import Carry
import InnerRules

/-!
# Inside a nested run: the same counter, with a moving right end

When a carry reaches a leftmost block of even length `1^(6j+6)` and the first digit is 1, the machine starts a
nested run (`nest_sweep`): the leftmost block becomes `1^3` followed by `2j+1` digits 0, and the head turns back
**before** reaching the right end of the tape.  From then on the part of the tape left of the head is again a
counter, swept by *inner sweeps*, and the part right of it is the region the outer left pass went over (each passed
digit 1 left as the word `0 0 1 0 1 0`, `tok`).  The right end of the inner counter has two phases:

* `X L ds W`:  `L [ds] 0 1 1 E>1 0 W`
* `Yc L ds W`: `L [ds] 0 1 1 1 0 F>0 1 0 W`

and an inner sweep is the outer sweep with other end pieces (`InnerRules.lean`): the digits change by exactly the
same rule as in `sweep_zero` / `sweep_even` (the shared core `core_zero`, `core_even`, for any tape `T` right of the
left pass), the phase alternates, and every sweep from phase X eats one passed digit 1 of the region on the right
(`inner_X_zero`, `inner_X_even`, `inner_Y_zero`, `inner_Y_even`): the inner counter grows into the passed region
three cells per sweep, as the outer counter grows into blank tape.

Not covered here: inner sweeps that reach the inner left end, passed digits other than 1 (their words
`0 0 (1 0)^(3k+2)` are eaten in a different phase pattern), and the end of the nested run when the passed region is
used up.  Everything here is checked by Lean's kernel.
-/

namespace H115779

open TM

/-- A passed digit 1, as the outer left pass leaves it: `0 0 1 0 1 0`. -/
def tok (W : Tape) : Tape := app [false, false, true, false, true, false] W

theorem modR_zero (ks : List Nat) (T : Tape) : modR (0 :: ks) T = tok (modR ks T) := rfl

/-- Phase X of the inner right end. -/
def X (L : Tape) (ds : List Nat) (W : Tape) : Config :=
  ⟨cons true (cons true (cons false (enc ds L))), cons true (cons false W), .E⟩

/-- Phase Y of the inner right end. -/
def Yc (L : Tape) (ds : List Nat) (W : Tape) : Config :=
  ⟨cons false (cons true (cons true (cons true (cons false (enc ds L))))), cons false (cons true (cons false W)), .F⟩

/-! ## The core of a sweep, for any tape right of the left pass -/

theorem core_zero (Lc : Tape) (ks : List Nat) (T : Tape) :
    steps (9 + lcost ks + rcost ks) ⟨enc ([0] ++ odds ks) Lc, cons false T, .D⟩ =
      some ⟨app [true, true, true] (rpass ks (cons true Lc)), T, .A⟩ := by
  have h1 := left_pass Lc ks [0] T
  have e2 : enc [0] Lc = cons true (cons true (rep 0 [true, true] (cons false Lc))) := rfl
  rw [e2] at h1
  have h2 := left_even 0 Lc (modR ks T)
  have h3 : steps 4 ⟨Lc, cons false (cons false (cons true (rep 0 [false, true] (cons false (modR ks T))))), .E⟩ =
      some ⟨app [true, true, true] (cons true Lc), modR ks T, .A⟩ :=
    turn_zero Lc _
  have h4 := right_pass ks (cons true Lc) T
  exact steps_congr trans (by omega) (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4)))

theorem core_even (Lc : Tape) (i : Nat) (ks : List Nat) (T : Tape) :
    steps (9 + 10 * (2 * i + 2) + lcost ks + rcost ks) ⟨enc ([2 * i + 2] ++ odds ks) Lc, cons false T, .D⟩ =
      some ⟨app [true, true, true] (rpass ks (rep i [false, true, true, false, true, true]
        (app [false, true, true, false, true, true, true] Lc))), T, .A⟩ := by
  have h1 := left_pass Lc ks [2 * i + 2] T
  have e1 : enc [2 * i + 2] Lc = cons true (cons true (rep (3 * i + 3) [true, true] (cons false Lc))) := by
    show app (ones (3 * (2 * i + 2) + 2)) (cons false Lc) = _
    rw [show 3 * (2 * i + 2) + 2 = 2 * (3 * i + 3) + 2 by omega, app_ones_even]
  rw [e1] at h1
  have h2 := left_even (3 * i + 3) Lc (modR ks T)
  have e2 : rep (3 * i + 3) [false, true] (cons false (modR ks T)) =
      app [false, true, false, true, false, true] (rep i [false, true, false, true, false, true]
        (cons false (modR ks T))) := by
    rw [show 3 * i + 3 = 3 * (i + 1) by omega, rep_mul3]; rfl
  rw [e2] at h2
  have h3 : steps (8 * i + 12) ⟨Lc, cons false (cons false (cons true (app [false, true, false, true, false, true]
      (rep i [false, true, false, true, false, true] (cons false (modR ks T)))))), .E⟩ =
      some ⟨app [true, true, true] (rep i [false, true, true, false, true, true]
        (app [false, true, true, false, true, true, true] Lc)), modR ks T, .A⟩ := by
    rw [rot3]; exact turn_even i Lc _
  have h4 := right_pass ks (rep i [false, true, true, false, true, true]
    (app [false, true, true, false, true, true, true] Lc)) T
  exact steps_congr trans (by omega) (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4)))

/-- Closing the block in hand (`1^5`) gives the digits of `stepD`. -/
theorem close (L : Tape) (ks E : List Nat) (c : Nat) :
    app [true, true, true, true, true] (rpass ks (app (ones (3 * c)) (cons false (enc E L)))) =
      enc (stepD E c ks) L := by
  have h := congrArg (fun x : Config => tail (tail x.l)) (F_rpass L ks E c)
  simpa [F, P] using h

theorem open_zero (L : Tape) (Y : List Nat) (a : Nat) :
    cons true (enc (Y ++ [a]) L) = app (ones (3 * (a + 1))) (cons false (enc Y L)) := by
  rw [enc_snoc, show 3 * (a + 1) = 1 + (3 * a + 2) by omega, app_ones_add 1 (3 * a + 2)]; rfl

theorem open_even (L : Tape) (Y : List Nat) (a i : Nat) :
    rep i [false, true, true, false, true, true] (app [false, true, true, false, true, true, true]
      (enc (Y ++ [a]) L)) = app (ones (3 * 0)) (cons false (enc (Y ++ [a + 1] ++ List.replicate (2 * i + 1) 0) L)) := by
  rw [enc_zeros, enc_snoc, enc_snoc, rep_add (2 * i) 1, rep_mul2]
  rw [show app [false, true, true, false, true, true, true] (app (ones (3 * a + 2)) (cons false (enc Y L))) =
    cons false (rep 1 [true, true, false] (app (ones (3 * (a + 1) + 2)) (cons false (enc Y L)))) by
      rw [show 3 * (a + 1) + 2 = 3 + (3 * a + 2) by omega, app_ones_add 3 (3 * a + 2)]; rfl]
  exact (rep_rotate i [false] [true, true, false, true, true, false] [false, true, true, false, true, true] rfl _).symm

/-! ## The inner sweeps -/

/-- **An inner sweep from phase X, stopping at a digit 0**: the digits change as in `sweep_zero`, one passed digit
1 is eaten, and the end goes to phase Y. -/
theorem inner_X_zero (L : Tape) (Y : List Nat) (a : Nat) (ks : List Nat) (W : Tape) :
    steps (21 + lcost ks + rcost ks) (X L (Y ++ [a, 0] ++ odds ks) (tok W)) = some (Yc L (stepD Y (a + 1) ks) W) := by
  have h0 := x_left (enc (Y ++ [a, 0] ++ odds ks) L) (cons false (tok W))
  have h1 := core_zero (enc (Y ++ [a]) L) ks (cons false (cons false (cons true (cons false (tok W)))))
  rw [← enc_append, show Y ++ [a] ++ ([0] ++ odds ks) = Y ++ [a, 0] ++ odds ks by simp] at h1
  have h2 := x_right (rpass ks (cons true (enc (Y ++ [a]) L))) W
  unfold Yc X
  rw [← close L ks Y (a + 1), ← open_zero]
  exact steps_congr trans (by omega) (steps_seq trans h0 (steps_seq trans h1 h2))

/-- **An inner sweep from phase X, stopping at a digit `2i+2`.** -/
theorem inner_X_even (L : Tape) (Y : List Nat) (a i : Nat) (ks : List Nat) (W : Tape) :
    steps (21 + 10 * (2 * i + 2) + lcost ks + rcost ks) (X L (Y ++ [a, 2 * i + 2] ++ odds ks) (tok W)) =
      some (Yc L (stepD (Y ++ [a + 1] ++ List.replicate (2 * i + 1) 0) 0 ks) W) := by
  have h0 := x_left (enc (Y ++ [a, 2 * i + 2] ++ odds ks) L) (cons false (tok W))
  have h1 := core_even (enc (Y ++ [a]) L) i ks (cons false (cons false (cons true (cons false (tok W)))))
  rw [← enc_append, show Y ++ [a] ++ ([2 * i + 2] ++ odds ks) = Y ++ [a, 2 * i + 2] ++ odds ks by simp] at h1
  have h2 := x_right (rpass ks (rep i [false, true, true, false, true, true]
    (app [false, true, true, false, true, true, true] (enc (Y ++ [a]) L)))) W
  unfold Yc X
  rw [← close L ks (Y ++ [a + 1] ++ List.replicate (2 * i + 1) 0) 0, ← open_even]
  exact steps_congr trans (by omega) (steps_seq trans h0 (steps_seq trans h1 h2))

/-- **An inner sweep from phase Y, stopping at a digit 0**: the end goes back to phase X; nothing is eaten. -/
theorem inner_Y_zero (L : Tape) (Y : List Nat) (a : Nat) (ks : List Nat) (W : Tape) :
    steps (21 + lcost ks + rcost ks) (Yc L (Y ++ [a, 0] ++ odds ks) W) = some (X L (stepD Y (a + 1) ks) W) := by
  have h0 := y_left (enc (Y ++ [a, 0] ++ odds ks) L) W
  have h1 := core_zero (enc (Y ++ [a]) L) ks
    (cons false (cons false (cons true (cons false (cons true (cons true (cons false W)))))))
  rw [← enc_append, show Y ++ [a] ++ ([0] ++ odds ks) = Y ++ [a, 0] ++ odds ks by simp] at h1
  have h2 := y_right (rpass ks (cons true (enc (Y ++ [a]) L))) W
  unfold X
  rw [← close L ks Y (a + 1), ← open_zero]
  exact steps_congr trans (by omega) (steps_seq trans h0 (steps_seq trans h1 h2))

/-- **An inner sweep from phase Y, stopping at a digit `2i+2`.** -/
theorem inner_Y_even (L : Tape) (Y : List Nat) (a i : Nat) (ks : List Nat) (W : Tape) :
    steps (21 + 10 * (2 * i + 2) + lcost ks + rcost ks) (Yc L (Y ++ [a, 2 * i + 2] ++ odds ks) W) =
      some (X L (stepD (Y ++ [a + 1] ++ List.replicate (2 * i + 1) 0) 0 ks) W) := by
  have h0 := y_left (enc (Y ++ [a, 2 * i + 2] ++ odds ks) L) W
  have h1 := core_even (enc (Y ++ [a]) L) i ks
    (cons false (cons false (cons true (cons false (cons true (cons true (cons false W)))))))
  rw [← enc_append, show Y ++ [a] ++ ([2 * i + 2] ++ odds ks) = Y ++ [a, 2 * i + 2] ++ odds ks by simp] at h1
  have h2 := y_right (rpass ks (rep i [false, true, true, false, true, true]
    (app [false, true, true, false, true, true, true] (enc (Y ++ [a]) L)))) W
  unfold X
  rw [← close L ks (Y ++ [a + 1] ++ List.replicate (2 * i + 1) 0) 0, ← open_even]
  exact steps_congr trans (by omega) (steps_seq trans h0 (steps_seq trans h1 h2))

/-! ## The start of a nested run -/

/-- **The start of a nested run**: every digit odd, the first one 1, the leftmost block `1^(6j+6)`.  The sweep
does not come back to the right end: the leftmost block becomes `1^3` and `2j+1` digits 0, with the inner right
end in phase Y, and right of it the region the left pass went over (`modR ks T0`, the other digits as words
`0 0 (1 0)^(3k+2)`, then the old right end). -/
theorem nest_sweep (j : Nat) (ks : List Nat) :
    steps (8 + lcost (0 :: ks) + (20 * j + 26)) (P (raw (6 * j + 6)) (odds (0 :: ks))) =
      some (Yc (raw 3) (List.replicate (2 * j + 1) 0) (modR ks T0)) := by
  have h0 := tail_left (enc (odds (0 :: ks)) (raw (6 * j + 6)))
  have h1 := left_pass (raw (6 * j + 6)) (0 :: ks) [] T0
  rw [List.nil_append] at h1
  have h2 := nest_start j (modR ks T0)
  have e1 : (⟨enc [] (raw (6 * j + 6)), cons false (modR (0 :: ks) T0), .D⟩ : Config) =
      ⟨rep j [true, true, true, true, true, true] (cons true (cons true (cons true (cons true (cons true
        (cons true blank)))))), cons false (cons false (cons false (cons true (cons false (cons true (cons false
        (modR ks T0))))))), .D⟩ := by
    show (⟨app (ones (6 * j + 6)) blank, _, _⟩ : Config) = _
    rw [app_ones_six]; rfl
  rw [e1] at h1
  have e2 : cons false (cons true (cons true (rep j [true, false, true, true, false, true] (cons true (cons false
      (cons true (cons true (cons false (cons true (cons true (cons true blank))))))))))) =
      cons false (cons true (cons true (cons true (cons false (enc (List.replicate (2 * j + 1) 0) (raw 3)))))) := by
    rw [show List.replicate (2 * j + 1) 0 = [] ++ List.replicate (2 * j + 1) 0 from rfl, enc_zeros, rep_add (2 * j) 1,
      rep_mul2]
    have := rep_rotate j [true, false] [true, true, false, true, true, false] [true, false, true, true, false, true]
      rfl (app [true, true, false, true, true, true] blank)
    show app [false, true, true] (rep j [true, false, true, true, false, true] (app [true, false]
      (app [true, true, false, true, true, true] blank))) = _
    rw [← this]; rfl
  rw [e2] at h2
  exact steps_congr trans (by omega) (steps_seq trans h0 (steps_seq trans h1 h2))

end H115779
