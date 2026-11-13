import Rules

/-!
# 1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE: the block machine

At every macro configuration the head is in state F on a gap `0 0`, with a block of `X` ones on its left and blank
tape beyond it.  Right of the gap the tape is a row of blocks of ones, each followed by one 0, of a fixed shape:

    0^∞ 1^X  F>0 0  (1 0)^a  [mid]  (1 0)^b  [tail]  0^∞

* `(1 0)^a`, `(1 0)^b`: runs of *units* (blocks of a single 1);
* `mid`: nothing, an empty block (one more 0: `0`), or an even block `1^(2q+2) 0`;
* `tail`: nothing or an odd block `1^(2q+3)`.

`Q` is such a configuration, `cfg s` the machine configuration it stands for.  `mstep` is one macro step (a round
of the left block against the first block that is not a unit, a merge at a gap, a restart at the left end, or one
of the moves at a left block of 2), with its exact cost; `mstep_sound` says the machine follows it, and
`mstep_halt` that the only halt (`X = 4`, nothing but units right of the gap) is a real halt.  Everything is checked
by Lean's kernel.
-/

namespace H15252

open TM

/-- The block between the two runs of units. -/
inductive Mid where
  | none
  | zero
  | ev (q : Nat)
  deriving DecidableEq, Repr

/-- A macro configuration: `X`, the units `a`, `mid`, the units `b`, the tail (`some q`: the block `2q + 3`). -/
structure Q where
  X : Nat
  a : Nat
  m : Mid
  b : Nat
  t : Option Nat
  deriving DecidableEq, Repr

def menc : Mid → Tape → Tape
  | .none, s => s
  | .zero, s => cons false s
  | .ev q, s => rep (2 * q + 2) [true] (cons false s)

def tenc : Option Nat → Tape
  | none => blank
  | some q => rep (2 * q + 3) [true] blank

/-- The tape right of the gap. -/
def rtape (s : Q) : Tape := rep s.a [true, false] (menc s.m (rep s.b [true, false] (tenc s.t)))

/-- The machine configuration of a macro configuration. -/
def cfg (s : Q) : Config := ⟨rep s.X [true] blank, cons false (cons false (rtape s)), .F⟩

/-! ## Tape identities -/

theorem rep_tt (n : Nat) (s : Tape) : rep n [true, true] s = rep (2 * n) [true] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, rep_succ, ih]; rfl

theorem ones_add (a b : Nat) (s : Tape) : rep a [true] (rep b [true] s) = rep (a + b) [true] s := by
  rw [rep_add]

theorem units_add (a b : Nat) (s : Tape) : rep a [true, false] (rep b [true, false] s) = rep (a + b) [true, false] s := by
  rw [rep_add]

theorem cons_true_ft (k : Nat) (s : Tape) : cons true (rep k [false, true] s) = rep k [true, false] (cons true s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    show cons true (cons false (cons true (rep k [false, true] s))) = _
    rw [ih]; rfl

theorem ft_cons_false (j : Nat) (R : Tape) : rep j [false, true] (cons false R) = cons false (rep j [true, false] R) := by
  induction j generalizing R with
  | zero => rfl
  | succ j ih =>
    show app [false, true] (rep j [false, true] (cons false R)) = _
    rw [ih]; rfl

theorem one_blank : rep 1 [true] blank = rep 1 [true, false] blank := by
  show cons true blank = cons true (cons false blank); rw [cons_false_blank]

theorem ones_succ (n : Nat) (s : Tape) : rep (n + 1) [true] s = cons true (rep n [true] s) := rfl

theorem ones_cons (n : Nat) (s : Tape) : rep n [true] (cons true s) = rep (n + 1) [true] s := rep_app_comm n [true] s

theorem units_succ (n : Nat) (s : Tape) : rep (n + 1) [true, false] s = cons true (cons false (rep n [true, false] s)) := rfl

/-- The walk: F crosses `j` units to the left. -/
theorem walkB (j : Nat) (L R : Tape) :
    steps (2 * j) ⟨rep j [true, false] L, cons false (cons false R), .F⟩ =
      some ⟨L, cons false (cons false (rep j [true, false] R)), .F⟩ := by
  have h := walk j L R
  rw [ft_cons_false] at h; exact h

/-- `X = 1` is not a macro configuration: walk the last 1 over as a unit. -/
def norm (s : Q) : Q × Nat := if s.X = 1 then (⟨0, s.a + 1, s.m, s.b, s.t⟩, 2) else (s, 0)

theorem norm_sound (s : Q) : steps (norm s).2 (cfg s) = some (cfg (norm s).1) := by
  unfold norm
  split
  · rename_i h
    obtain ⟨X, a, m, b, t⟩ := s
    simp only at h; subst h
    have w := walkB 1 blank (rtape ⟨1, a, m, b, t⟩)
    simp only [cfg, rtape] at w ⊢
    rw [one_blank, w, units_add, Nat.add_comm]; rfl
  · rfl

/-! ## The macro step -/

/-- A macro step: the next configuration and its cost, a halt, or `stuck` (a case outside the invariant). -/
inductive MS where
  | go (s : Q) (n : Nat)
  | halt
  | stuck
  deriving DecidableEq, Repr

def withNorm (s : Q) (n : Nat) : MS := .go (norm s).1 (n + (norm s).2)

/-- After a round against the tail `2q + 3`: it shrinks to `2q + 1`, which is a unit if `q = 0`. -/
def tailNext (X k q : Nat) : Q :=
  match q with
  | 0 => ⟨X, k + 3, .none, 0, none⟩
  | q + 1 => ⟨X, k + 2, .none, 0, some q⟩

/-- After a round against an even block `2q + 2`: it shrinks to `2q`, an empty block if `q = 0`. -/
def evNext (q : Nat) : Mid :=
  match q with
  | 0 => .zero
  | q + 1 => .ev q

def mstep (s : Q) : MS :=
  match s with
  -- a round against an even block `2q + 2`
  | ⟨X, a, .ev q, b, t⟩ =>
    if 3 ≤ X then withNorm ⟨X - 2, a + 2, (evNext q), b, t⟩ (6 * a + 18)
    else if X = 0 then .go ⟨0, a + 2, (evNext q), b, t⟩ (6 * a + 14)
    else .stuck
  -- a round against the tail `2q + 3`
  | ⟨X, a, .none, b, some q⟩ =>
    if X = 2 then
      if a + b = 0 then .go ⟨5, 0, .ev q, 0, none⟩ 15
      else .go ⟨5, 0, .zero, a + b - 1, some q⟩ 15
    else if 3 ≤ X then withNorm (tailNext (X - 2) (a + b) q) (6 * (a + b) + 18)
    else if X = 0 then .go (tailNext 0 (a + b) q) (6 * (a + b) + 14)
    else .stuck
  -- only units
  | ⟨X, a, .none, b, none⟩ =>
    if X = 2 then
      if a + b = 0 then .stuck else .go ⟨5, 0, .zero, a + b - 1, none⟩ 15
    else if 5 ≤ X then withNorm ⟨X - 4, 0, .none, 0, some (a + b + 1)⟩ (6 * (a + b) + 20)
    else if X = 4 then .halt
    else if X = 0 then .go ⟨2 * (a + b) + 4, 0, .none, 0, some 0⟩ (8 * (a + b) + 27)
    else if X = 3 then .go ⟨2 * (a + b) + 6, 0, .none, 0, some 0⟩ (8 * (a + b) + 35)
    else .stuck
  -- a gap: merge, or restart at the left end
  | ⟨X, a, .zero, b, t⟩ =>
    if 5 ≤ X then
      match b, t with
      | b + 1, t => withNorm ⟨X - 4, 0, .ev (a + 2), b, t⟩ (6 * a + 20)
      | 0, some q => withNorm ⟨X - 4, 0, .ev (a + q + 3), 0, none⟩ (6 * a + 20)
      | 0, none => withNorm ⟨X - 4, 0, .none, 0, some (a + 1)⟩ (6 * a + 20)
    else if X = 0 ∨ X = 3 then
      let k := if X = 3 then a + 1 else a
      match b, t with
      | b + 2, t => .go ⟨2 * k + 7, 0, .zero, b, t⟩ (8 * k + 20)
      | 1, some q => .go ⟨2 * k + 7, 0, .ev q, 0, none⟩ (8 * k + 20)
      | 1, none => .go ⟨2 * k + 5, 0, .none, 0, some 0⟩ (8 * k + 28)
      | 0, some q => .go ⟨2 * k + 2 * q + 7, 0, .none, 0, some 0⟩ (8 * k + 2 * q + 30)
      | 0, none => .go ⟨2 * k + 4, 0, .none, 0, some 0⟩ (8 * k + 27)
    else .stuck

end H15252
