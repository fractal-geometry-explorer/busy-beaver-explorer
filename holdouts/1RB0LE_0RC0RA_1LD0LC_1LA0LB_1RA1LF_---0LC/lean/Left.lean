import Count
import LeftParts
import LeftRules

/-!
# The carries into the left part, as moves between phase-R configurations

`LeftRules.lean` (generated) proves the runs on the tape as `symtm` writes them; here they are restated on `R`:

* `fe k` (k < 17): a carry out of the all-ones counter of `2j+2` units into `L_k` gives the zero counter and `L_{k+1}`.
* `s1`: the carry into `L_17` runs to the left end of the tape.  The counter becomes the 24 (here `j`) blocks
  `1^9 0 1 0` of the new left part `L1 j = P (1^9 0 1 0)^j Q`, the wall of `2p+2` units becomes a counter of
  `2p+3` units holding `1, 3, 0, 3, 0, …, 3, 0` (`ds1 p`), and the new wall is empty.
* `fo k` (k < 6): the first six carries into `L1`, with the odd counter of `2q+3` units; they only change `Q`.

All for every `j`, `n`, `p`, `q` (and every tape left of `Q` in `fo`).  Checked by Lean's kernel.
-/

namespace H136111

open TM

/-- The tape left of the counter: `L_k`, then blank tape. -/
def Lt (k : Nat) : Tape := app (lk k) blank

/-- `L1 j = P (1^9 0 1 0)^j Q`, then blank tape. -/
def L1t (j : Nat) : Tape := app qQ (rep j bB (app pP blank))

/-- `k` pairs `3, 0` (a `Y3` and an `X0`). -/
def d30 : Nat → List Nat
  | 0 => []
  | k + 1 => 3 :: 0 :: d30 k

/-- The counter made from the wall of `2p+2` units: `1, 3, 0, …, 3, 0`, `2p+3` units. -/
def ds1 (p : Nat) : List Nat := 1 :: d30 (p + 1)

theorem enc_d30 (k : Nat) (L : Tape) : enc false (d30 k) L = rep k (x0 ++ x0) L := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [d30, enc, yw, xw, rep_succ, ← app_app, ih]

theorem rep_double (k : Nat) (w : List Bool) (T : Tape) : rep (2 * k) w T = rep k (w ++ w) T := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, rep_succ, rep_succ, ih, rep_succ, app_app]

/-! ## Phase R written the way the rules start and end -/

theorem start_even (j n : Nat) (T : Tape) :
    R (top true (2 * j + 2)) n T = ⟨rep n w6 (app tl (app x0 (rep (j + 1) (x1 ++ x0) T))), blank, .B⟩ := by
  rw [top_even]
  simp only [R, enc, xw]
  rw [enc_ones, show enc false [3] T = app x0 T from rfl, rep_rotate j x1 (x0 ++ x1) (x1 ++ x0) rfl, app_app x1 x0 T,
    rep_app_comm]

theorem start_odd (q n : Nat) (T : Tape) :
    R (top true (2 * q + 3)) n T = ⟨rep n w6 (app tl (app x0 (rep (q + 1) (x1 ++ x0) (app x1 T)))), blank, .B⟩ := by
  rw [show 2 * q + 3 = 2 * (q + 1) + 1 by omega, top_odd]
  simp only [R, enc, xw]
  rw [show ones (q + 1) = ones (q + 1) ++ [] by simp, enc_ones, rep_rotate (q + 1) x1 (x0 ++ x1) (x1 ++ x0) rfl]
  rfl

theorem start_s1 (j p : Nat) (T : Tape) :
    R (top true (2 * j + 2)) (2 * p + 2) T =
      ⟨rep (p + 1) (w6 ++ w6) (app tl (app x0 (rep (j + 1) (x1 ++ x0) T))), blank, .B⟩ := by
  rw [start_even, show 2 * p + 2 = 2 * (p + 1) by omega, rep_double]

theorem w6_split (S : Tape) : app w6 S = app [true, true, true, false] (app [true, false] S) := rfl

theorem end_even (j n : Nat) (T : Tape) :
    R (bot true (2 * j + 2)) (n + 2) T =
      ⟨app [true, true, true, false] (rep (n + 1) [true, false, true, true, true, false]
        (app [true, false, true, true, true, false, true, false, true, true, true, true, true, false, true, true, true,
          true, true, true, true, false]
          (rep j [true, true, true, false, true, true, true, true, true, true, true, false] (app [true, true, true] T)))),
        blank, .B⟩ := by
  rw [bot_even]
  simp only [R, enc, xw]
  rw [enc_zeros]
  show (⟨rep (n + 1 + 1) w6 (app tl (app x0 (app x0 (rep j (x1 ++ x0) (app x1 T))))), blank, .B⟩ : Config) = _
  rw [← rep_app_comm, w6_split, ← rep_rotate (n + 1) [true, true, true, false] [true, false, true, true, true, false] w6 rfl]
  rw [show app x1 T = app [true, true, false] (app [true, true, true] T) from rfl,
    ← rep_rotate j [true, true, false] [true, true, true, false, true, true, true, true, true, true, true, false]
      (x1 ++ x0) rfl]
  rfl

theorem end_odd (q n : Nat) (T : Tape) :
    R (bot true (2 * q + 3)) (n + 2) T =
      ⟨app [true, true, true, false] (rep (n + 1) [true, false, true, true, true, false]
        (app [true, false, true, true, true, false, true, false, true, true, true, true, true, false, true, true, true,
          true, true, true, true, false]
          (rep q [true, true, true, false, true, true, true, true, true, true, true, false]
            (app [true, true, true, false, true, true, true, true, true] T)))),
        blank, .B⟩ := by
  rw [show 2 * q + 3 = 2 * (q + 1) + 1 by omega, bot_odd]
  simp only [R, enc, xw]
  rw [show zeros (q + 1) = zeros (q + 1) ++ [] by simp, enc_zeros]
  show (⟨rep (n + 1 + 1) w6 (app tl (app x0 (app x0 (rep (q + 1) (x1 ++ x0) T)))), blank, .B⟩ : Config) = _
  rw [← rep_app_comm, w6_split, ← rep_rotate (n + 1) [true, true, true, false] [true, false, true, true, true, false] w6 rfl]
  rw [rep_succ q (x1 ++ x0) T, show app (x1 ++ x0) (rep q (x1 ++ x0) T) =
      app [true, true, false] (app [true, true, true, false, true, true, true, true, true]
        (rep q (x1 ++ x0) T)) from rfl,
    rep_rotate q [true, true, true, false, true, true, true, true, true] (x1 ++ x0)
      [true, true, true, false, true, true, true, true, true, true, true, false] rfl]
  rfl

theorem end_s1 (j p : Nat) :
    R (ds1 p) 0 (L1t j) =
      ⟨app [true, true, true, false, true, false, true, true, true, true, true, true, true, false, true, true, true,
          false, true, true, true, true]
        (rep p [true, false, true, true, true, true, true, false, true, true, true, true]
          (app [true, false, true, true, true, true, true, false, true, false, true, false]
            (rep j [true, true, true, true, true, false, true, false, true, true, true, true]
              (app [true, true, true, true, true] (app pP blank))))),
        blank, .B⟩ := by
  simp only [R, ds1, enc, xw, rep_zero]
  rw [enc_d30, L1t, show app qQ (rep j bB (app pP blank)) = app [false, true, false, true, false]
      (app [true, true, true, true, true] (rep j bB (app pP blank))) from rfl,
    rep_rotate j [true, true, true, true, true] bB [true, true, true, true, true, false, true, false, true, true, true, true] rfl,
    ← rep_app_comm,
    show app (x0 ++ x0) (app [false, true, false, true, false] (rep j [true, true, true, true, true, false, true, false, true, true, true, true]
        (app [true, true, true, true, true] (app pP blank)))) =
      app [false, true, true, true, true] (app [true, false, true, true, true, true, true, false, true, false, true, false]
        (rep j [true, true, true, true, true, false, true, false, true, true, true, true]
        (app [true, true, true, true, true] (app pP blank)))) from rfl,
    ← rep_rotate p [false, true, true, true, true] [true, false, true, true, true, true, true, false, true, true, true, true]
      (x0 ++ x0) rfl]
  rfl

/-! ## The rules on phase R -/

theorem fe (k : Nat) (hk : k < 17) (j n : Nat) :
    ∃ t, steps t (R (top true (2 * j + 2)) (n + 1) (Lt k)) = some (R (bot true (2 * j + 2)) (n + 2) (Lt (k + 1))) := by
  rw [start_even, end_even]
  match k, hk with
  | 0, _ => exact ⟨_, fe_run_0 j n⟩
  | 1, _ => exact ⟨_, fe_run_1 j n⟩
  | 2, _ => exact ⟨_, fe_run_2 j n⟩
  | 3, _ => exact ⟨_, fe_run_3 j n⟩
  | 4, _ => exact ⟨_, fe_run_4 j n⟩
  | 5, _ => exact ⟨_, fe_run_5 j n⟩
  | 6, _ => exact ⟨_, fe_run_6 j n⟩
  | 7, _ => exact ⟨_, fe_run_7 j n⟩
  | 8, _ => exact ⟨_, fe_run_8 j n⟩
  | 9, _ => exact ⟨_, fe_run_9 j n⟩
  | 10, _ => exact ⟨_, fe_run_10 j n⟩
  | 11, _ => exact ⟨_, fe_run_11 j n⟩
  | 12, _ => exact ⟨_, fe_run_12 j n⟩
  | 13, _ => exact ⟨_, fe_run_13 j n⟩
  | 14, _ => exact ⟨_, fe_run_14 j n⟩
  | 15, _ => exact ⟨_, fe_run_15 j n⟩
  | 16, _ => exact ⟨_, fe_run_16 j n⟩
  | k + 17, h => exact absurd h (by omega)

theorem s1 (j p : Nat) :
    ∃ t, steps t (R (top true (2 * j + 2)) (2 * p + 2) (Lt 17)) = some (R (ds1 p) 0 (L1t j)) := by
  rw [start_s1, end_s1]
  exact ⟨_, s1_run j p⟩


theorem fo (k : Nat) (hk : k < 6) (q n : Nat) (PB : Tape) :
    ∃ t, steps t (R (top true (2 * q + 3)) (n + 1) (app (qk k) PB)) =
      some (R (bot true (2 * q + 3)) (n + 2) (app (qk (k + 1)) PB)) := by
  rw [start_odd, end_odd]
  match k, hk with
  | 0, _ => exact ⟨_, fo_run_0 n q PB⟩
  | 1, _ => exact ⟨_, fo_run_1 n q PB⟩
  | 2, _ => exact ⟨_, fo_run_2 n q PB⟩
  | 3, _ => exact ⟨_, fo_run_3 n q PB⟩
  | 4, _ => exact ⟨_, fo_run_4 n q PB⟩
  | 5, _ => exact ⟨_, fo_run_5 n q PB⟩

end H136111
