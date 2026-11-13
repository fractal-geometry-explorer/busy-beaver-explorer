import Collide

/-!
# Q configurations with raw gaps, and a normal form for tapes

`Macro.lean` writes the counter's gaps as `3p + 2`, which is all the regular steps meet.  The irregular steps
also meet the *misaligned* gaps (length `3p` or `3p + 1`), so here a Q configuration lists the raw gap lengths:

    qr W a G  =  W 0 1^(3a) B>0 0^g₁ 1 0^g₂ 1 … 0^gₙ 1 0^∞

with `W` the word, last block first (as in `Macro.lean`), `a ≥ 1` the counter's low part and `G = [g₁, …, gₙ]`.
`zc L G` is the configuration in the middle of a one-unit step, after the word has been rewritten (state A).

The lemmas `nf_*` rewrite a tape term into a normal form (repeats expanded where the count is a successor, single
cells moved inside a repeat of a word they rotate); `simp only [nf]` brings the statements of the generated rules
and of their restatements to the same term, which is how the restatements in `CollideQ.lean` are proved.
-/

namespace H70169

open TM

/-- The gaps `0^g 1` with raw lengths `g`, then blank tape. -/
def gl : List Nat → Tape
  | [] => blank
  | g :: G => rep g [false] (cons true (gl G))

/-- Blocks (last first), each followed by a 0, in front of the tape `X`; `wl` is `wlx · blank` up to the last 0. -/
def wlx : List Nat → Tape → Tape
  | [], X => X
  | b :: W, X => rep b [true] (cons false (wlx W X))

/-- The Q configuration `W 0 1^(3a) B>0` followed by the raw gaps `G`. -/
def qr (W : List Nat) (a : Nat) (G : List Nat) : Config :=
  ⟨rep a [true, true, true] (cons false (wl W)), cons false (gl G), .B⟩

/-- The configuration `W' 0 1 1 A>0 1` followed by the gaps `G`, where `L` is the tape left of the new word's 0
(`wl W'` in use). -/
def zc (L : Tape) (G : List Nat) : Config := ⟨cons true (cons true (cons false L)), cons false (cons true (gl G)), .A⟩

theorem gl_twos (n : Nat) (G : List Nat) : gl (List.replicate n 2 ++ G) = rep n [false, false, true] (gl G) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, gl, ih]; rfl

theorem gl_twos_blank (n : Nat) : gl (List.replicate n 2) = rep n [false, false, true] blank := by
  have h := gl_twos n []
  rwa [List.append_nil] at h

theorem wlx_ones (n : Nat) (X : Tape) : wlx (List.replicate n 1) X = rep n [true, false] X := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, wlx, ih]; rfl

theorem wlx_append (C D : List Nat) (X : Tape) : wlx (C ++ D) X = wlx C (wlx D X) := by
  induction C with
  | nil => rfl
  | cons c C ih => simp only [List.cons_append, wlx, ih]

theorem wl_append (C W : List Nat) : wl (C ++ W) = wlx C (wl W) := by
  induction C with
  | nil => rfl
  | cons c C ih => simp only [List.cons_append, wl, wlx, ih]

theorem rep_mul2 (s : Nat) (w : List Bool) (X : Tape) : rep (2 * s) w X = rep s (w ++ w) X := by
  induction s with
  | zero => rfl
  | succ s ih => rw [show 2 * (s + 1) = 2 * s + 1 + 1 by omega, rep_succ, rep_succ, ih, rep_succ, app_app]

theorem rep_mul3 (s : Nat) (w : List Bool) (X : Tape) : rep (3 * s) w X = rep s (w ++ w ++ w) X := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [show 3 * (s + 1) = 3 * s + 1 + 1 + 1 by omega, rep_succ, rep_succ, rep_succ, ih, rep_succ, app_app, app_app]

theorem rep_mul2_succ (s : Nat) (w : List Bool) (X : Tape) : rep (2 * s + 1) w X = rep s (w ++ w) (app w X) := by
  rw [← rep_mul2, rep_add]; rfl

theorem rep_mul3_succ (s : Nat) (w : List Bool) (X : Tape) : rep (3 * s + 1) w X = rep s (w ++ w ++ w) (app w X) := by
  rw [← rep_mul3, rep_add]; rfl

theorem rep_mul3_succ2 (s : Nat) (w : List Bool) (X : Tape) :
    rep (3 * s + 2) w X = rep s (w ++ w ++ w) (app w (app w X)) := by
  rw [← rep_mul3, rep_add]; rfl

theorem rep_mul3_succ3 (s : Nat) (w : List Bool) (X : Tape) :
    rep (3 * s + 3) w X = rep s (w ++ w ++ w) (app w (app w (app w X))) := by
  rw [← rep_mul3, rep_add]; rfl

/-- A single cell moves inside a repeat of a word it rotates. -/
theorem rot_in (n : Nat) (b : Bool) (w : List Bool) (X : Tape) :
    cons b (rep n (w ++ [b]) X) = rep n (b :: w) (cons b X) :=
  rep_rotate n [b] (w ++ [b]) (b :: w) (by simp) X

theorem nf_t1 (n : Nat) (X : Tape) : cons true (rep n [true] X) = rep n [true] (cons true X) := rot_in n true [] X
theorem nf_f1 (n : Nat) (X : Tape) : cons false (rep n [false] X) = rep n [false] (cons false X) := rot_in n false [] X
theorem nf_t2 (n : Nat) (X : Tape) : cons true (rep n [true, true] X) = rep n [true, true] (cons true X) :=
  rot_in n true [true] X
theorem nf_t3 (n : Nat) (X : Tape) : cons true (rep n [true, true, true] X) = rep n [true, true, true] (cons true X) :=
  rot_in n true [true, true] X
theorem nf_f3 (n : Nat) (X : Tape) :
    cons false (rep n [false, false, false] X) = rep n [false, false, false] (cons false X) := rot_in n false [false, false] X
theorem nf_tf (n : Nat) (X : Tape) :
    cons true (cons false (rep n [true, false] X)) = rep n [true, false] (cons true (cons false X)) :=
  rep_rotate n [true, false] [true, false] [true, false] rfl X
theorem nf_ft (n : Nat) (X : Tape) :
    cons false (cons true (rep n [false, true] X)) = rep n [false, true] (cons false (cons true X)) :=
  rep_rotate n [false, true] [false, true] [false, true] rfl X
theorem nf_ft6 (n : Nat) (X : Tape) :
    cons false (cons true (rep n [false, true, false, true, false, true] X))
      = rep n [false, true, false, true, false, true] (cons false (cons true X)) :=
  rep_rotate n [false, true] [false, true, false, true, false, true] [false, true, false, true, false, true] rfl X
theorem nf_tf6 (n : Nat) (X : Tape) :
    cons true (cons false (rep n [true, false, true, false, true, false] X))
      = rep n [true, false, true, false, true, false] (cons true (cons false X)) :=
  rep_rotate n [true, false] [true, false, true, false, true, false] [true, false, true, false, true, false] rfl X
theorem nf_f_tf6 (n : Nat) (X : Tape) :
    cons false (rep n [true, false, true, false, true, false] X)
      = rep n [false, true, false, true, false, true] (cons false X) :=
  rep_rotate n [false] [true, false, true, false, true, false] [false, true, false, true, false, true] rfl X
theorem nf_ffttt (n : Nat) (X : Tape) :
    cons false (cons false (cons true (rep n [false, false, true] X))) = rep n [false, false, true] (cons false (cons false (cons true X))) :=
  rep_rotate n [false, false, true] [false, false, true] [false, false, true] rfl X
theorem nf_fft6 (n : Nat) (X : Tape) :
    cons false (cons false (cons true (rep n [false, false, true, false, false, true] X)))
      = rep n [false, false, true, false, false, true] (cons false (cons false (cons true X))) :=
  rep_rotate n [false, false, true] [false, false, true, false, false, true] [false, false, true, false, false, true] rfl X
theorem nf_ones_even (n : Nat) (X : Tape) : rep (2 * n) [true] X = rep n [true, true] X := rep_mul2 n [true] X
theorem nf_ones_three (n : Nat) (X : Tape) : rep (3 * n) [true] X = rep n [true, true, true] X := rep_mul3 n [true] X

end H70169
