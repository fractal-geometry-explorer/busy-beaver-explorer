import Sweep

/-!
# 1RB0RF_1LC0RA_1LD1LB_0LE---_1LA0LA_1RE1LD: the inner counter of a cycle (F-phase), exactly

After the sweep of `Sweep.lean` the tape is `1 (01)^N 0 0` with the head in F at the right end (`Fs N`, from
`C(n)` with N = n+1: `to_fs`).  The inner counter is `X p q r` = `0^inf 1 (01)^p 1 B> 1 (01)^q (11)^r 0^inf`:
p copies of `01` on the left, the head block `1 (01)^q (11)^r` at the right end.  Its moves (rules in
`Rules.lean`):

* round (`x_round`): X(p+2, q, r+1) -> X(p, q+3, r);
* restart (`x_restart`): X(p+1, q, 0) -> X(p, 1, q+1);
* ends (`x_end0`, `x_end1`, `x_end00`): with no copies (or one) left on the left, the head goes to the left end in
  state A: `Lev (x, m, s)` = `0^inf A> 0 x (01)^m (11)^s 0^inf`.

`g p q r` is the resulting end, and `xrun`: X(p, q, r) reaches `Lev (g p q r)` for every p, r and q ≥ 1, by
recursion on p.  So `fphase`: `Fs N` reaches `Lev (g N 1 0)`; no halt is possible in this part of a cycle.
-/

namespace H10442

open TM

/-- `0^inf 1 (01)^p 1 B> 1 (01)^q (11)^r 0^inf`. -/
def X (p q r : Nat) : Config :=
  ⟨cons true (rep p [true, false] (cons true blank)), cons true (rep q [false, true] (rep r [true, true] blank)), .B⟩

/-- `0^inf 1 (01)^N 0 0 F> 0^inf`. -/
def Fs (N : Nat) : Config := ⟨cons false (cons false (rep N [true, false] (cons true blank))), blank, .F⟩

/-- `0^inf A> 0 x (01)^m (11)^s 0^inf` (x = 1 when the first component is 1), the head on the blank cell. -/
def Lev : Nat × Nat × Nat → Config
  | (x, m, s) => ⟨blank, cons false (cons (x == 1) (rep m [false, true] (rep s [true, true] blank))), .A⟩

theorem rep_tt (n : Nat) (s : Tape) : cons true (rep n [true, true] (cons true s)) = rep (n + 1) [true, true] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show cons true (cons true (cons true (rep n [true, true] (cons true s)))) = rep (n + 2) [true, true] s
    rw [ih]; rfl

theorem of_steps {c c' d d' : Config} {n : Nat} (h : steps n c = some c') (e : d = c) (e' : d' = c') :
    Reaches d d' := ⟨n, by rw [e, e']; exact h⟩

/-- The end of the inner counter from X(p, q, r). -/
def g : Nat → Nat → Nat → Nat × Nat × Nat
  | 0, q, 0 => (1, 1, q + 1)
  | 0, q, r + 1 => (0, q + 2, r)
  | 1, q, r + 1 => (1, q + 3, r)
  | p + 1, q, 0 => g p 1 (q + 1)
  | p + 2, q, r + 1 => g p (q + 3) r

theorem round (p q r : Nat) : Reaches (X (p + 2) q (r + 1)) (X p (q + 3) r) := ⟨_, x_round p q _ _⟩

theorem restart (p q : Nat) : Reaches (X (p + 1) q 0) (X p 1 (q + 1)) :=
  of_steps (x_restart p q _) rfl (by simp only [X]; rw [← rep_tt]; rfl)

/-- **The inner counter: X(p, q+1, r) reaches `Lev (g p (q+1) r)`.** -/
theorem xrun : ∀ p q r, Reaches (X p (q + 1) r) (Lev (g p (q + 1) r))
  | 0, q, 0 => of_steps (x_end00 q) rfl (by simp only [g, Lev]; rw [← rep_tt]; rfl)
  | 0, q, r + 1 => of_steps (x_end0 q _) rfl rfl
  | 1, q, r + 1 => of_steps (x_end1 q _) rfl rfl
  | p + 1, q, 0 => by
    rw [show g (p + 1) (q + 1) 0 = g p (0 + 1) (q + 1 + 1) by simp [g]]
    exact (restart p (q + 1)).trans (xrun p 0 (q + 1 + 1))
  | p + 2, q, r + 1 => by
    rw [show g (p + 2) (q + 1) (r + 1) = g p (q + 3 + 1) r by simp [g]]
    exact (round p (q + 1) r).trans (xrun p (q + 3) r)

theorem to_fs (x : Nat) :
    Reaches ⟨blank, cons true (cons true (rep x [true, true] blank)), .C⟩ (Fs (2 * x + 3)) := by
  refine (ones_to_pairs x).trans (of_steps (y_run (2 * x + 2)) rfl ?_)
  simp only [Fs]; rw [← rep_app_comm]; rfl

/-- **`C(2x+2)` reaches `Lev (g (2x+3) 1 0)`: the first two parts of a cycle.** -/
theorem fphase (x : Nat) :
    Reaches ⟨blank, cons true (cons true (rep x [true, true] blank)), .C⟩ (Lev (g (2 * x + 3) 1 0)) :=
  (to_fs x).trans ((of_steps (x_start _) rfl rfl).trans (xrun (2 * x + 3) 0 0))

/-- The last part of a cycle (after the transitions): `0^inf 1 (01)^m 0 A>` reaches `C(2m+4)`. -/
theorem to_c (m : Nat) :
    Reaches ⟨cons false (rep m [true, false] (cons true blank)), blank, .A⟩
      ⟨blank, cons true (cons true (rep (m + 1) [true, true] blank)), .C⟩ :=
  of_steps (fin m) rfl (by rw [← rep_tt])

end H10442
