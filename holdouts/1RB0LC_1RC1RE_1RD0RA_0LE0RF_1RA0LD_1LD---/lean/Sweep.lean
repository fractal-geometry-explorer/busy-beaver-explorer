import Rules

/-!
# One sweep of the counter, for every digit list

The tape is read as **digits**: a digit `d` is a block `0 1^(3d+2)` (a separator, then `3d+2` ones).  A sweep
configuration (`P L ds`) is

    L  0 1^(3d₁+2)  0 1^(3d₂+2)  …  0 1^(3dₘ+2)  0 1 B>0   (blank to the right)

with any tape `L` on the left.  From the right end the head walks left over the digits.  Every block of odd length
(odd digit) is passed and rewritten (`left_odd`); the first block of even length (even digit `b`) stops it
(`left_even`); the head turns there and walks back to the right end, rebuilding every block it passed (`turn_zero`,
`turn_even`, `right_odd`), now three cells further right, and the tape is again a sweep configuration.

On digits (`sweep_zero`, `sweep_even`): with `a` the digit left of the stop digit `b`, and odd digits
`2k₁+1, …, 2kₙ+1` right of it,

* `b = 0`:      `a 0 (2k₁+1) … (2kₙ+1)`  becomes  `(a+2) 0^(2k₁) 1 … 0^(2kₙ) 1`;
* `b = 2i+2`:   `a b (2k₁+1) … (2kₙ+1)`  becomes  `(a+1) 0^(b-1) 1 0^(2k₁) 1 … 0^(2kₙ) 1`,

in `21 + 10 b + Σ (20 kⱼ + 16)` steps.  The digit `a` can also be a block of any length that is not a digit, such as
the leftmost block (`raw_zero`, `raw_even`: a block `1^r` at the left end of the tape grows by 6 or by 3).

Everything here is checked by Lean's kernel.
-/

namespace H115779

open TM

/-! ## Words -/

/-- `n` ones. -/
def ones : Nat → List Bool
  | 0 => []
  | n + 1 => true :: ones n

theorem app_ones_add (a b : Nat) (T : Tape) : app (ones (a + b)) T = app (ones a) (app (ones b) T) := by
  induction a with
  | zero => simp [ones]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [ones, app_cons, ih]

theorem app_ones_odd (n : Nat) (T : Tape) : app (ones (2 * n + 1)) T = rep n [true, true] (cons true T) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 + (2 * n + 1) by omega, app_ones_add, ih]
    rfl

theorem app_ones_even (n : Nat) (T : Tape) :
    app (ones (2 * n + 2)) T = cons true (cons true (rep n [true, true] T)) := by
  rw [show 2 * n + 2 = 1 + (2 * n + 1) by omega, app_ones_add, app_ones_odd]
  rw [show app (ones 1) (rep n [true, true] (cons true T)) = cons true (rep n [true, true] (cons true T)) from rfl]
  congr 1
  exact (rep_rotate n [true] [true, true] [true, true] rfl T).symm

theorem rep_mul2 (m : Nat) (w : List Bool) (T : Tape) : rep (2 * m) w T = rep m (w ++ w) T := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 + 2 * m by omega, rep_add, ih]
    show rep 2 w (rep m (w ++ w) T) = app (w ++ w) (rep m (w ++ w) T)
    simp [rep, app_app]

theorem rep_mul3 (m : Nat) (w : List Bool) (T : Tape) : rep (3 * m) w T = rep m (w ++ w ++ w) T := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show 3 * (m + 1) = 3 + 3 * m by omega, rep_add, ih]
    show rep 3 w (rep m (w ++ w ++ w) T) = app (w ++ w ++ w) (rep m (w ++ w ++ w) T)
    simp [rep, app_app]

/-! ## Digits -/

/-- The tape left of the head, nearest cell first, for digits `ds` (left to right) written as blocks `0 1^(3d+2)`
after the tape `L`. -/
def enc : List Nat → Tape → Tape
  | [], L => L
  | d :: ds, L => enc ds (app (ones (3 * d + 2)) (cons false L))

theorem enc_append (xs ys : List Nat) (L : Tape) : enc (xs ++ ys) L = enc ys (enc xs L) := by
  induction xs generalizing L with
  | nil => rfl
  | cons x xs ih => exact ih _

theorem enc_snoc (xs : List Nat) (d : Nat) (L : Tape) :
    enc (xs ++ [d]) L = app (ones (3 * d + 2)) (cons false (enc xs L)) := by
  rw [enc_append]; rfl

theorem enc_zeros (xs : List Nat) (m : Nat) (L : Tape) :
    enc (xs ++ List.replicate m 0) L = rep m [true, true, false] (enc xs L) := by
  induction m generalizing xs with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, show xs ++ 0 :: List.replicate m 0 = (xs ++ [0]) ++ List.replicate m 0 by simp,
      ih, enc_snoc]
    exact rep_app_comm m [true, true, false] (enc xs L)

/-- A sweep configuration: `L 0 1^(3d₁+2) … 0 1^(3dₘ+2) 0 1 B>0`, blank to the right. -/
def P (L : Tape) (ds : List Nat) : Config := ⟨cons true (cons false (enc ds L)), blank, .B⟩

/-- The odd digits `2k+1` for `k ∈ ks`. -/
def odds (ks : List Nat) : List Nat := ks.map (fun k => 2 * k + 1)

/-! ## The left pass -/

/-- What the left pass leaves right of the head after passing the odd digits `2k+1`, `k ∈ ks`. -/
def modR : List Nat → Tape → Tape
  | [], T => T
  | k :: ks, T => cons false (cons false (rep (3 * k + 2) [true, false] (modR ks T)))

def lcost : List Nat → Nat
  | [] => 0
  | k :: ks => 12 * k + 10 + lcost ks

/-- The head (D, on the separator after the digits `X ++ odds ks`) walks left over the odd digits. -/
theorem left_pass (L : Tape) : ∀ (ks X : List Nat) (T : Tape),
    steps (lcost ks) ⟨enc (X ++ odds ks) L, cons false T, .D⟩ = some ⟨enc X L, cons false (modR ks T), .D⟩
  | [], X, T => by simp [odds, lcost, modR]
  | k :: ks, X, T => by
    have h1 := left_pass L ks (X ++ [2 * k + 1]) T
    rw [show X ++ odds (k :: ks) = (X ++ [2 * k + 1]) ++ odds ks by simp [odds]]
    rw [enc_snoc, show 3 * (2 * k + 1) + 2 = 2 * (3 * k + 2) + 1 by omega, app_ones_odd] at h1
    have h2 := left_odd (3 * k + 2) (enc X L) (modR ks T)
    exact steps_congr trans (by simp [lcost]; omega) (steps_seq trans h1 h2)

/-! ## The right pass -/

/-- What the right pass writes for the odd digits `2k+1`, `k ∈ ks`, behind the `1 1 1` it carries. -/
def rpass : List Nat → Tape → Tape
  | [], Z => Z
  | k :: ks, Z => rpass ks (rep k [false, true, true, false, true, true] (app [false, true, true, true, true, true] Z))

def rcost : List Nat → Nat
  | [] => 0
  | k :: ks => 8 * k + 6 + rcost ks

/-- `1 1 1` in front of a re-bracketed repeat. -/
theorem rot3 (k : Nat) (X : Tape) :
    app [true, true, true] (rep k [false, true, true, false, true, true] X) =
      cons true (rep k [true, true, false, true, true, false] (app [true, true] X)) := by
  show cons true (app [true, true] (rep k [false, true, true, false, true, true] X)) = _
  rw [rep_rotate k [true, true] [false, true, true, false, true, true] [true, true, false, true, true, false] rfl]

theorem rep_3k2 (k : Nat) (R : Tape) :
    rep (3 * k + 2) [true, false] R = app [true, false, true, false] (rep k [true, false, true, false, true, false] R) := by
  rw [show 3 * k + 2 = 2 + 3 * k by omega, rep_add, rep_mul3]; rfl

theorem right_odd' (k : Nat) (Z R : Tape) :
    steps (8 * k + 6) ⟨app [true, true, true] Z, cons false (cons false (rep (3 * k + 2) [true, false] R)), .A⟩ =
      some ⟨app [true, true, true] (rep k [false, true, true, false, true, true]
        (app [false, true, true, true, true, true] Z)), R, .A⟩ := by
  rw [rep_3k2, rot3]
  exact right_odd k Z R

theorem right_pass : ∀ (ks : List Nat) (Z T : Tape),
    steps (rcost ks) ⟨app [true, true, true] Z, modR ks T, .A⟩ = some ⟨app [true, true, true] (rpass ks Z), T, .A⟩
  | [], Z, T => by simp [rcost, modR, rpass]
  | k :: ks, Z, T => by
    have h1 := right_odd' k Z (modR ks T)
    have h2 := right_pass ks (rep k [false, true, true, false, true, true]
      (app [false, true, true, true, true, true] Z)) T
    exact steps_congr trans (by simp [rcost]) (steps_seq trans h1 h2)

/-! ## A whole sweep, for any tape left of the stop digit -/

/-- What the left pass leaves at the right end (`tail_left`). -/
def T0 : Tape := cons false (cons false (cons true (cons false blank)))

/-- The right end after the left pass, as `tail_right` reads it. -/
theorem tail_blank : T0 = cons false (cons false (cons true blank)) := by
  show cons false (cons false (cons true (cons false blank))) = _
  rw [cons_false_blank]

/-- The final form of a sweep: `1 1 1` in hand at the right end becomes `1^5 0 1 B>0`. -/
def F (Z : Tape) : Config := ⟨cons true (cons false (app [true, true, true, true, true] Z)), blank, .B⟩

/-- A sweep that stops at a digit 0, with any tape `Lc` left of it. -/
theorem sweep_zero_gen (Lc : Tape) (ks : List Nat) :
    steps (21 + lcost ks + rcost ks) ⟨cons true (cons false (enc ([0] ++ odds ks) Lc)), blank, .B⟩ =
      some (F (rpass ks (cons true Lc))) := by
  have h0 := tail_left (enc ([0] ++ odds ks) Lc)
  have h1 := left_pass Lc ks [0] T0
  have e2 : enc [0] Lc = cons true (cons true (rep 0 [true, true] (cons false Lc))) := rfl
  rw [e2] at h1
  have h2 := left_even 0 Lc (modR ks T0)
  have h3 : steps 4 ⟨Lc, cons false (cons false (cons true (rep 0 [false, true] (cons false (modR ks T0))))), .E⟩ =
      some ⟨app [true, true, true] (cons true Lc), modR ks T0, .A⟩ :=
    turn_zero Lc _
  have h4 := right_pass ks (cons true Lc) T0
  have h5 := tail_right (rpass ks (cons true Lc))
  rw [← tail_blank] at h5
  refine steps_congr trans ?_
    (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 h5)))))
  omega

/-- A sweep that stops at a digit `2i+2`, with any tape `Lc` left of it. -/
theorem sweep_even_gen (Lc : Tape) (i : Nat) (ks : List Nat) :
    steps (21 + 10 * (2 * i + 2) + lcost ks + rcost ks)
      ⟨cons true (cons false (enc ([2 * i + 2] ++ odds ks) Lc)), blank, .B⟩ =
      some (F (rpass ks (rep i [false, true, true, false, true, true]
        (app [false, true, true, false, true, true, true] Lc)))) := by
  have h0 := tail_left (enc ([2 * i + 2] ++ odds ks) Lc)
  have h1 := left_pass Lc ks [2 * i + 2] T0
  have e1 : enc [2 * i + 2] Lc = cons true (cons true (rep (3 * i + 3) [true, true] (cons false Lc))) := by
    show app (ones (3 * (2 * i + 2) + 2)) (cons false Lc) = _
    rw [show 3 * (2 * i + 2) + 2 = 2 * (3 * i + 3) + 2 by omega, app_ones_even]
  rw [e1] at h1
  have h2 := left_even (3 * i + 3) Lc (modR ks T0)
  have e2 : rep (3 * i + 3) [false, true] (cons false (modR ks T0)) =
      app [false, true, false, true, false, true] (rep i [false, true, false, true, false, true]
        (cons false (modR ks T0))) := by
    rw [show 3 * i + 3 = 3 * (i + 1) by omega, rep_mul3]; rfl
  rw [e2] at h2
  have h3 : steps (8 * i + 12) ⟨Lc, cons false (cons false (cons true (app [false, true, false, true, false, true]
      (rep i [false, true, false, true, false, true] (cons false (modR ks T0)))))), .E⟩ =
      some ⟨app [true, true, true] (rep i [false, true, true, false, true, true]
        (app [false, true, true, false, true, true, true] Lc)), modR ks T0, .A⟩ := by
    rw [rot3]; exact turn_even i Lc _
  have h4 := right_pass ks (rep i [false, true, true, false, true, true]
    (app [false, true, true, false, true, true, true] Lc)) T0
  have h5 := tail_right (rpass ks (rep i [false, true, true, false, true, true]
    (app [false, true, true, false, true, true, true] Lc)))
  rw [← tail_blank] at h5
  refine steps_congr trans ?_
    (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 h5)))))
  omega

/-! ## Back to digits -/

/-- The digits a sweep writes: `E` finished, an open block that will become the digit `c+1`, then for each odd
digit `2k+1` passed: the open block is closed, `2k` zeros follow and a new block is opened. -/
def stepD : List Nat → Nat → List Nat → List Nat
  | E, c, [] => E ++ [c + 1]
  | E, c, k :: ks => stepD (E ++ [c + 1] ++ List.replicate (2 * k) 0) 0 ks

/-- Closing an open block of `m` ones (after the `1 1 1` in hand): it gets `5` more ones. -/
theorem close_block (k m : Nat) (W : Tape) :
    rep k [false, true, true, false, true, true] (app [false, true, true, true, true, true] (app (ones m) W)) =
      cons false (rep (2 * k) [true, true, false] (app (ones (m + 5)) W)) := by
  have e : app [false, true, true, true, true, true] (app (ones m) W) = cons false (app (ones (m + 5)) W) := by
    rw [show m + 5 = 5 + m by omega, app_ones_add]; rfl
  rw [e, rep_mul2]
  exact (rep_rotate k [false] [true, true, false, true, true, false] [false, true, true, false, true, true] rfl _).symm

/-- The final form of a sweep, as digits. -/
theorem F_rpass (L : Tape) : ∀ (ks E : List Nat) (c : Nat),
    F (rpass ks (app (ones (3 * c)) (cons false (enc E L)))) = P L (stepD E c ks)
  | [], E, c => by
    show (⟨_, _, _⟩ : Config) = ⟨_, _, _⟩
    rw [rpass, stepD, enc_snoc, show 3 * (c + 1) + 2 = 5 + 3 * c by omega, app_ones_add]
    rfl
  | k :: ks, E, c => by
    have h := F_rpass L ks (E ++ [c + 1] ++ List.replicate (2 * k) 0) 0
    rw [stepD, ← h, rpass, close_block, enc_zeros, enc_snoc, show 3 * c + 5 = 3 * (c + 1) + 2 by omega]
    rfl

/-- **The sweep, stopping at a digit 0.**  `a 0 (2k₁+1) … (2kₙ+1)` becomes `(a+2) 0^(2k₁) 1 … 0^(2kₙ) 1`. -/
theorem sweep_zero (L : Tape) (Y : List Nat) (a : Nat) (ks : List Nat) :
    steps (21 + lcost ks + rcost ks) (P L (Y ++ [a, 0] ++ odds ks)) = some (P L (stepD Y (a + 1) ks)) := by
  have h := sweep_zero_gen (enc (Y ++ [a]) L) ks
  rw [← enc_append, show Y ++ [a] ++ ([0] ++ odds ks) = Y ++ [a, 0] ++ odds ks by simp] at h
  rw [← F_rpass L ks Y (a + 1)]
  have e : cons true (enc (Y ++ [a]) L) = app (ones (3 * (a + 1))) (cons false (enc Y L)) := by
    rw [enc_snoc, show 3 * (a + 1) = 1 + (3 * a + 2) by omega, app_ones_add 1 (3 * a + 2)]; rfl
  rw [e] at h
  exact h

/-- **The sweep, stopping at a digit `2i+2`.**  `a (2i+2) (2k₁+1) … (2kₙ+1)` becomes
`(a+1) 0^(2i+1) 1 0^(2k₁) 1 … 0^(2kₙ) 1`. -/
theorem sweep_even (L : Tape) (Y : List Nat) (a i : Nat) (ks : List Nat) :
    steps (21 + 10 * (2 * i + 2) + lcost ks + rcost ks) (P L (Y ++ [a, 2 * i + 2] ++ odds ks)) =
      some (P L (stepD (Y ++ [a + 1] ++ List.replicate (2 * i + 1) 0) 0 ks)) := by
  have h := sweep_even_gen (enc (Y ++ [a]) L) i ks
  rw [← enc_append, show Y ++ [a] ++ ([2 * i + 2] ++ odds ks) = Y ++ [a, 2 * i + 2] ++ odds ks by simp] at h
  rw [← F_rpass L ks (Y ++ [a + 1] ++ List.replicate (2 * i + 1) 0) 0]
  have e : rep i [false, true, true, false, true, true] (app [false, true, true, false, true, true, true]
      (enc (Y ++ [a]) L)) = app (ones (3 * 0)) (cons false (enc (Y ++ [a + 1] ++ List.replicate (2 * i + 1) 0) L)) := by
    rw [enc_zeros, enc_snoc, enc_snoc, rep_add (2 * i) 1, rep_mul2]
    rw [show app [false, true, true, false, true, true, true] (app (ones (3 * a + 2)) (cons false (enc Y L))) =
      cons false (rep 1 [true, true, false] (app (ones (3 * (a + 1) + 2)) (cons false (enc Y L)))) by
        rw [show 3 * (a + 1) + 2 = 3 + (3 * a + 2) by omega, app_ones_add 3 (3 * a + 2)]; rfl]
    exact (rep_rotate i [false] [true, true, false, true, true, false] [false, true, true, false, true, true] rfl _).symm
  rw [e] at h
  exact h

/-! ## At the left end: a block `1^r` that is not a digit -/

/-- The left end: blank tape, then a block of `r` ones. -/
def raw (r : Nat) : Tape := app (ones r) blank

/-- The digits after a sweep that stopped at the first digit (the block left of it is `raw r`). -/
def rawD : List Nat → List Nat
  | [] => []
  | k :: ks => stepD (List.replicate (2 * k) 0) 0 ks

/-- The first digit is 0 and every digit after it is odd: the left block grows by 6. -/
theorem raw_zero (r : Nat) (ks : List Nat) :
    steps (21 + lcost ks + rcost ks) (P (raw r) ([0] ++ odds ks)) = some (P (raw (r + 6)) (rawD ks)) := by
  have h := sweep_zero_gen (raw r) ks
  have e : cons true (raw r) = app (ones (r + 1)) blank := by
    rw [raw, show r + 1 = 1 + r by omega, app_ones_add 1 r]; rfl
  rw [e] at h
  cases ks with
  | nil =>
    have e1 : app [true, true, true, true, true] (app (ones (r + 1)) blank) = raw (r + 6) := by
      rw [raw, show r + 6 = 5 + (r + 1) by omega, app_ones_add 5 (r + 1)]; rfl
    rw [rpass, F, e1] at h
    exact h
  | cons k ks =>
    have e2 : cons false (rep (2 * k) [true, true, false] (app (ones (r + 1 + 5)) blank)) =
        app (ones (3 * 0)) (cons false (enc (List.replicate (2 * k) 0) (raw (r + 6)))) := by
      rw [show List.replicate (2 * k) 0 = [] ++ List.replicate (2 * k) 0 from rfl, enc_zeros]; rfl
    rw [rpass, close_block, e2, F_rpass] at h
    exact h

/-- The first digit is `2i+2` and every digit after it is odd: the left block grows by 3. -/
theorem raw_even (r i : Nat) (ks : List Nat) :
    steps (21 + 10 * (2 * i + 2) + lcost ks + rcost ks) (P (raw r) ([2 * i + 2] ++ odds ks)) =
      some (P (raw (r + 3)) (stepD (List.replicate (2 * i + 1) 0) 0 ks)) := by
  have h := sweep_even_gen (raw r) i ks
  rw [← F_rpass (raw (r + 3)) ks (List.replicate (2 * i + 1) 0) 0]
  have e : rep i [false, true, true, false, true, true] (app [false, true, true, false, true, true, true] (raw r)) =
      app (ones (3 * 0)) (cons false (enc (List.replicate (2 * i + 1) 0) (raw (r + 3)))) := by
    rw [show List.replicate (2 * i + 1) 0 = [] ++ List.replicate (2 * i + 1) 0 from rfl, enc_zeros,
      rep_add (2 * i) 1, rep_mul2]
    rw [show app [false, true, true, false, true, true, true] (raw r) =
      cons false (rep 1 [true, true, false] (enc [] (raw (r + 3)))) by
        rw [raw, raw, show r + 3 = 3 + r by omega, app_ones_add 3 r]; rfl]
    exact (rep_rotate i [false] [true, true, false, true, true, false] [false, true, true, false, true, true] rfl _).symm
  rw [e] at h
  exact h

/-- The cost of a sweep in closed form: `lcost ks + rcost ks = Σ (20 k + 16)`. -/
theorem cost_sum : ∀ ks : List Nat, lcost ks + rcost ks = (ks.map (fun k => 20 * k + 16)).sum
  | [] => rfl
  | k :: ks => by simp [lcost, rcost, ← cost_sum ks]; omega

end H115779
