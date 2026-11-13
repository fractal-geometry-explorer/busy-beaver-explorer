import Halt
import Fallback

/-!
# 1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB: the drain rules chained into one map

The macro configurations of the README, as Lean data. The environment is a list of blocks `(g, c)`, each the tape
`0^g (10)^c 1`, then blank tape (`envT`). The nodes:

* `d A B e` : `0^inf 1^A (01)^B 0 C> 0 Z`          (the drain)
* `p A B e` : `0^inf 1^A (01)^B 1 1 1 0 C> 0 Z`    (the parity tail)
* `t n e`   : `0^inf E> (01)^n Z`                  (the head at the left end)

with `Z = envT e`. `F` makes one macro move: one sweep, one odd sweep, an absorbed block, the end of a drain, a
parity tail, or a left-end phase; each case is a rule of `Macro.lean`/`Halt.lean`/`Fallback.lean` restated here.
Outputs are put in a normal form (`canon`: a block `0 (10)^c 1` right after another block is merged into it; `mkT`:
the left-end phase absorbs a first block with one 0). Some small environments are not covered by any rule here; `F`
returns `stuck` there. The orbit from blank tape meets none of them in its first 3·10^7 nodes (`orbit_native`).

Main results:
* `F_sem`: `F n = next n'` → the machine goes from `n` to `n'` in at least one step; `F n = halt` → it halts;
* `halts_of_orbit`, `not_halts_of_orbit`, `halts_iff_of_no_stuck`: if the orbit of the start `d 1 0 []` (reached
  from blank tape in 2 steps) never gets stuck, the machine halts from blank tape iff the orbit reaches `halt`;
  an orbit that reaches `halt` before getting stuck proves a halt, and one that never reaches `halt` or `stuck`
  proves the machine runs for ever.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace H8002

open TM

/-! ## Tapes -/

/-- The environment: blocks `0^g (10)^c 1`, then blank tape. -/
def envT : List (Nat × Nat) → Tape
  | [] => blank
  | (g, c) :: e => rep g [false] (rep c [true, false] (cons true (envT e)))

/-- Put a block in front of an environment, merging the next block if it follows after a single 0:
`0^g (10)^c 1 0 (10)^c' 1 = 0^g (10)^(c+c'+1) 1`. -/
def mergeHd (x : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [x]
  | (g', c') :: e => if g' = 1 then (x.1, x.2 + c' + 1) :: e else x :: (g', c') :: e

/-- The normal form of an environment: no block after the first has a gap of one 0. -/
def canon : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | x :: e => mergeHd x (canon e)

/-- Drop k zeros from the front of an environment (k ≤ its first gap). -/
def shrink (k : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | (g, c) :: e => (g - k, c) :: e

theorem merge_eq (g c c' : Nat) (X : Tape) :
    rep g [false] (rep c [true, false] (cons true (rep 1 [false] (rep c' [true, false] (cons true X)))))
      = rep g [false] (rep (c + c' + 1) [true, false] (cons true X)) := by
  have : c + c' + 1 = c + (c' + 1) := by omega
  rw [this, rep_add]
  rfl

theorem envT_mergeHd (x : Nat × Nat) (e : List (Nat × Nat)) : envT (mergeHd x e) = envT (x :: e) := by
  obtain ⟨g, c⟩ := x
  cases e with
  | nil => rfl
  | cons y e =>
    obtain ⟨g', c'⟩ := y
    by_cases h : g' = 1
    · subst h
      show envT ((g, c + c' + 1) :: e) = _
      exact (merge_eq g c c' (envT e)).symm
    · show envT (if g' = 1 then _ else _) = _
      rw [if_neg h]

theorem envT_canon (e : List (Nat × Nat)) : envT (canon e) = envT e := by
  induction e with
  | nil => rfl
  | cons x e ih =>
    show envT (mergeHd x (canon e)) = _
    rw [envT_mergeHd]
    obtain ⟨g, c⟩ := x
    show rep g [false] (rep c [true, false] (cons true (envT (canon e)))) = _
    rw [ih]; rfl

/-! ## Normal forms of tapes -/

theorem n_ones (n : Nat) (s : Tape) : rep n [true] (cons true s) = rep (n + 1) [true] s := rep_app_comm n [true] s
theorem n_ones_ones (a b : Nat) (s : Tape) : rep a [true] (rep b [true] s) = rep (a + b) [true] s := (rep_add a b _ s).symm
theorem n_cons_one (n : Nat) (s : Tape) : cons true (rep n [true] s) = rep (n + 1) [true] s := rfl
theorem n_zeros (n : Nat) (s : Tape) : rep n [false] (cons false s) = rep (n + 1) [false] s := rep_app_comm n [false] s
theorem n_cons_zero (n : Nat) (s : Tape) : cons false (rep n [false] s) = rep (n + 1) [false] s := rfl
theorem n_zeros_zeros (a b : Nat) (s : Tape) : rep a [false] (rep b [false] s) = rep (a + b) [false] s :=
  (rep_add a b _ s).symm
theorem n_tf (n : Nat) (s : Tape) : rep n [true, false] (cons true (cons false s)) = rep (n + 1) [true, false] s :=
  rep_app_comm n [true, false] s
theorem n_cons_tf (n : Nat) (s : Tape) : cons true (cons false (rep n [true, false] s)) = rep (n + 1) [true, false] s :=
  rfl
theorem n_tf_tf (a b : Nat) (s : Tape) : rep a [true, false] (rep b [true, false] s) = rep (a + b) [true, false] s :=
  (rep_add a b _ s).symm
theorem n_two (n : Nat) (s : Tape) : rep n [true, true] s = rep (2 * n) [true] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show app [true, true] (rep n [true, true] s) = rep (2 * n + 1 + 1) [true] s
    rw [ih]; rfl
theorem n_tftf (n : Nat) (s : Tape) : rep n [true, false, true, false] s = rep (2 * n) [true, false] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show app [true, false, true, false] (rep n [true, false, true, false] s) = rep (2 * n + 1 + 1) [true, false] s
    rw [ih]; rfl
theorem n_ftft (n : Nat) (s : Tape) : rep n [false, true, false, true] s = rep (2 * n) [false, true] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show app [false, true, false, true] (rep n [false, true, false, true] s) = rep (2 * n + 1 + 1) [false, true] s
    rw [ih]; rfl
/-- Pairs `01` read one way are pairs `10` read the other: `1 (01)^b = (10)^b 1`. -/
theorem n_rot (b : Nat) (X : Tape) : cons true (rep b [false, true] X) = rep b [true, false] (cons true X) :=
  rep_rotate b [true] [false, true] [true, false] rfl X
theorem n_rot0 (b : Nat) (X : Tape) : rep b [false, true] (cons false X) = cons false (rep b [true, false] X) :=
  (rep_rotate b [false] [true, false] [false, true] rfl X).symm

macro "tnA" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [n_two, n_tftf, n_ftft, n_rot, n_rot0] $[$loc]?)
macro "tnB" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [n_ones, n_ones_ones, n_cons_one, n_zeros, n_cons_zero, n_zeros_zeros, n_tf, n_cons_tf, n_tf_tf, rep_zero, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul] $[$loc]?)
macro "tn" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| ((try tnA $[$loc]?); (try tnB $[$loc]?)))

/-! ## The nodes -/

/-- The left tape of a parity tail: `1^A (01)^B 1 1 1 0`, nearest the head first. -/
def Pl (A B : Nat) : Tape := cons false (cons true (cons true (cons true (rep B [true, false] (rep A [true] blank)))))

inductive Node where
  | d (A B : Nat) (e : List (Nat × Nat))
  | p (A B : Nat) (e : List (Nat × Nat))
  | t (n : Nat) (e : List (Nat × Nat))
  deriving DecidableEq, Repr

def Node.cfg : Node → Config
  | .d A B e => ⟨Dl A B blank, cons false (envT e), .C⟩
  | .p A B e => ⟨Pl A B, cons false (envT e), .C⟩
  | .t n e => ⟨blank, rep n [false, true] (envT e), .E⟩

/-! ## Reaching -/

def Reach (c c' : Config) : Prop := ∃ n, steps (n + 1) c = some c'
def Reaches (c c' : Config) : Prop := ∃ n, steps n c = some c'

theorem Reaches.trans {a b c : Config} : Reaches a b → Reaches b c → Reaches a c
  | ⟨n, h1⟩, ⟨m, h2⟩ => ⟨n + m, steps_seq H8002.trans h1 h2⟩
theorem reach_reaches {a b c : Config} : Reach a b → Reaches b c → Reach a c
  | ⟨n, h1⟩, ⟨m, h2⟩ => ⟨n + m, steps_congr H8002.trans (by omega) (steps_seq H8002.trans h1 h2)⟩
theorem Reach.reaches {a b : Config} : Reach a b → Reaches a b
  | ⟨n, h⟩ => ⟨n + 1, h⟩
theorem halts_pre {a b : Config} : Reaches a b → Halts H8002.trans b → Halts H8002.trans a
  | ⟨n, h1⟩, ⟨m, c, h2, h3⟩ => ⟨n + m, c, steps_seq H8002.trans h1 h2, h3⟩
theorem reach_of {n : Nat} {c c' : Config} (h : steps n c = some c') (hn : 0 < n) : Reach c c' :=
  ⟨n - 1, by rw [show n - 1 + 1 = n by omega]; exact h⟩
theorem reach_of' {n : Nat} {c c' d d' : Config} (h : steps n d = some d') (e1 : c = d) (e2 : c' = d') (hn : 0 < n) :
    Reach c c' := by
  subst e1; subst e2; exact reach_of h hn
theorem reach_eq {c c' c'' : Config} (h : Reach c c') (e : c' = c'') : Reach c c'' := e ▸ h

macro "cfgs" : tactic => `(tactic| simp only [Node.cfg, Dl, Pl, envT, shrink, rep_zero, rep_succ, app_cons, app_nil, cons_false_blank])
macro "rule" h:term : tactic =>
  `(tactic| (refine reach_of' $h ?_ ?_ (by omega) <;> ((try cfgs) <;> tn <;> (try simp only [Nat.add_comm, Nat.add_left_comm]))))

/-! ## The rules on the nodes -/

theorem r_sweep (a b g c : Nat) (e : List (Nat × Nat)) :
    Reach (Node.d (a + 3) b ((g + 3, c) :: e)).cfg (Node.d (a + 1) (b + 2) ((g + 1, c) :: e)).cfg := by
  rule sweep_D a b blank (rep (g + 2) [false] (rep c [true, false] (cons true (envT e))))

theorem r_sweep0 (a b : Nat) : Reach (Node.d (a + 3) b []).cfg (Node.d (a + 1) (b + 2) []).cfg := by
  rule sweep_D a b blank blank

theorem r_odd (a b c : Nat) (e : List (Nat × Nat)) :
    Reach (Node.d (a + 3) b ((1, c + 2) :: e)).cfg (Node.d (a + 1) (b + 3) ((1, c) :: e)).cfg := by
  rule odd_D a b c blank (envT e)

theorem r_oe1 (a b g c : Nat) (e : List (Nat × Nat)) :
    Reach (Node.d (a + 3) b ((1, 1) :: (g + 1, c) :: e)).cfg (Node.d (a + 1) (b + 3) ((g + 1, c) :: e)).cfg := by
  rule m_odd_end1 b (rep a [true] blank) (rep g [false] (rep c [true, false] (cons true (envT e))))
theorem r_oe1' (a b : Nat) : Reach (Node.d (a + 3) b [(1, 1)]).cfg (Node.d (a + 1) (b + 3) []).cfg := by
  rule m_odd_end1 b (rep a [true] blank) blank

theorem r_oe0 (a b g c : Nat) (e : List (Nat × Nat)) :
    Reach (Node.d (a + 3) b ((1, 0) :: (g + 5, c) :: e)).cfg (Node.p (a + 1) (b + 3) ((g, c) :: e)).cfg := by
  rule m_odd_end0 b (rep a [true] blank) (rep g [false] (rep c [true, false] (cons true (envT e))))
theorem r_oe0' (a b : Nat) : Reach (Node.d (a + 3) b [(1, 0)]).cfg (Node.p (a + 1) (b + 3) []).cfg := by
  rule m_odd_end0 b (rep a [true] blank) blank

/-- The tape after a block's first cell: a block `(10)^c 1` starts with a 1. -/
def afterOne (c : Nat) (X : Tape) : Tape :=
  match c with
  | 0 => X
  | k + 1 => cons false (rep k [true, false] (cons true X))
theorem block_one (c : Nat) (X : Tape) : rep c [true, false] (cons true X) = cons true (afterOne c X) := by
  cases c <;> rfl

theorem r_tail_halt (a b c : Nat) (e : List (Nat × Nat)) :
    Halts H8002.trans (Node.d (a + 3) b ((1, 0) :: (3, c) :: e)).cfg := by
  have h := m_tail_halt b (rep a [true] blank) (afterOne c (envT e))
  have e1 : (Node.d (a + 3) b ((1, 0) :: (3, c) :: e)).cfg = ⟨cons false (rep b [true, false] (cons true (cons true
      (cons true (rep a [true] blank))))), cons false (cons false (cons true (cons false (cons false (cons false (cons true
      (afterOne c (envT e)))))))), .C⟩ := by
    simp only [Node.cfg, Dl, envT, rep_zero, rep_succ, app_cons, app_nil]; rw [block_one c (envT e)]
  rw [e1]
  exact ⟨_, _, h, rfl⟩

theorem r_absorb (a b c g c' : Nat) (e : List (Nat × Nat)) :
    Reach (Node.d (a + 3) b ((2, c) :: (g + 1, c') :: e)).cfg (Node.d (a + 1) (b + c + 3) ((g, c') :: e)).cfg := by
  rule m_absorb b c (rep a [true] blank) (rep g [false] (rep c' [true, false] (cons true (envT e))))
theorem r_absorb' (a b c : Nat) : Reach (Node.d (a + 3) b [(2, c)]).cfg (Node.d (a + 1) (b + c + 3) []).cfg := by
  rule m_absorb b c (rep a [true] blank) blank

theorem r_end2 (b g c : Nat) (e : List (Nat × Nat)) :
    Reach (Node.d 2 b ((g + 1, c) :: e)).cfg (Node.d 1 0 ((1, b + 1) :: (g, c) :: e)).cfg := by
  rule m_end2 b (rep g [false] (rep c [true, false] (cons true (envT e))))
theorem r_end2' (b : Nat) : Reach (Node.d 2 b []).cfg (Node.d 1 0 [(1, b + 1)]).cfg := by
  rule m_end2 b blank

theorem r_end1 (b g c : Nat) (e : List (Nat × Nat)) :
    Reach (Node.d 1 b ((g + 1, c) :: e)).cfg (Node.t (b + 3) ((g, c) :: e)).cfg := by
  rule end1_D b (rep g [false] (rep c [true, false] (cons true (envT e))))
theorem r_end1' (b : Nat) : Reach (Node.d 1 b []).cfg (Node.t (b + 3) []).cfg := by
  rule end1_D b blank

theorem r_end0 (b g c : Nat) (e : List (Nat × Nat)) :
    Reach (Node.d 0 b ((g + 1, c) :: e)).cfg (Node.t (b + 2) ((g, c) :: e)).cfg := by
  rule m_end0 b (rep g [false] (rep c [true, false] (cons true (envT e))))
theorem r_end0' (b : Nat) : Reach (Node.d 0 b []).cfg (Node.t (b + 2) []).cfg := by
  rule m_end0 b blank

theorem r_tseg (n y : Nat) (e : List (Nat × Nat)) :
    Reach (Node.t (n + 1) ((0, y + 1) :: e)).cfg (Node.d (2 * n + 1) 0 ((1, y) :: e)).cfg := by
  rule m_tseg n y (envT e)

theorem r_tblank (n g c : Nat) (e : List (Nat × Nat)) :
    Reach (Node.t (n + 1) ((g + 5, c) :: e)).cfg (Node.d (2 * n + 4) 0 ((g + 1, c) :: e)).cfg := by
  rule m_tblank n (rep g [false] (rep c [true, false] (cons true (envT e))))
theorem r_tblank' (n : Nat) : Reach (Node.t (n + 1) []).cfg (Node.d (2 * n + 4) 0 []).cfg := by
  rule m_tblank n blank

theorem r_thalt (n c : Nat) (e : List (Nat × Nat)) : Halts H8002.trans (Node.t n ((2, c) :: e)).cfg := by
  have h := halt_001 n blank (afterOne c (envT e))
  have e1 : (Node.t n ((2, c) :: e)).cfg = ⟨blank, rep n [false, true] (cons false (cons false (cons true
      (afterOne c (envT e))))), .E⟩ := by
    simp only [Node.cfg, envT, rep_zero, rep_succ, app_cons, app_nil]; rw [block_one c (envT e)]
  rw [e1]; exact h

theorem r_peven (a k g c : Nat) (e : List (Nat × Nat)) :
    Reach (Node.p (a + 2) (2 * k) ((g + 5, c) :: e)).cfg (Node.d (a + 1) (2 * k + 4) ((g + 1, c) :: e)).cfg := by
  rule m_peven a k (rep g [false] (rep c [true, false] (cons true (envT e))))
theorem r_peven' (a k : Nat) : Reach (Node.p (a + 2) (2 * k) []).cfg (Node.d (a + 1) (2 * k + 4) []).cfg := by
  rule m_peven a k blank

theorem r_podd (a k g c : Nat) (e : List (Nat × Nat)) :
    Reach (Node.p a (2 * k + 1) ((g + 3, c) :: e)).cfg (Node.d 1 0 ((a + 1, 2 * k + 3) :: (g, c) :: e)).cfg := by
  rule m_podd a k (rep g [false] (rep c [true, false] (cons true (envT e))))
theorem r_podd' (a k : Nat) : Reach (Node.p a (2 * k + 1) []).cfg (Node.d 1 0 [(a + 1, 2 * k + 3)]).cfg := by
  rule m_podd a k blank

/-! ## The rules next to a block with no gap (`Fallback.lean`) -/

theorem r_f1 (a b c g c' : Nat) (e : List (Nat × Nat)) :
    Reach (Node.d (a + 3) b ((1, 1) :: (0, c) :: (g + 1, c') :: e)).cfg (Node.d (a + 1) (b + c + 4) ((g, c') :: e)).cfg := by
  rule f_oe1z b c (rep a [true] blank) (rep g [false] (rep c' [true, false] (cons true (envT e))))
theorem r_f1' (a b c : Nat) : Reach (Node.d (a + 3) b [(1, 1), (0, c)]).cfg (Node.d (a + 1) (b + c + 4) []).cfg := by
  rule f_oe1z b c (rep a [true] blank) blank

theorem r_f3 (a b c d : Nat) (e : List (Nat × Nat)) :
    Reach (Node.d (a + 3) b ((2, c) :: (0, d + 2) :: e)).cfg (Node.d (a + 1) (b + c + 4) ((1, d) :: e)).cfg := by
  rule f_ab_z b c d (rep a [true] blank) (envT e)

theorem r_f2o (a k c : Nat) (e : List (Nat × Nat)) :
    Reach (Node.d (a + 3) (2 * k + 1) ((1, 0) :: (0, c + 1) :: e)).cfg
      (Node.d 1 0 ((a + 2, 2 * k + 3) :: (0, c) :: e)).cfg := by
  rule f_oe0z_odd a c k (envT e)

theorem r_f2e (a k c : Nat) (e : List (Nat × Nat)) :
    Reach (Node.d (a + 3) (2 * k) ((1, 0) :: (0, c + 1) :: e)).cfg (Node.d (a + 2) 0 ((2, 2 * k + 1) :: (0, c) :: e)).cfg := by
  rule f_oe0z_even a c k (envT e)

/-! ## Normal forms of nodes -/

/-- The left-end phase, with the first blocks that have a gap of one 0 absorbed:
`(01)^n 0 (10)^c 1 = (01)^(n+c+1)`. -/
def mkT : Nat → List (Nat × Nat) → Node
  | n, (1, c) :: e => mkT (n + c + 1) e
  | n, e => .t n e

theorem t_absorb (n c : Nat) (X : Tape) :
    rep n [false, true] (cons false (rep c [true, false] (cons true X))) = rep (n + c + 1) [false, true] X := by
  rw [← n_rot0, show cons false (cons true X) = rep 1 [false, true] X from rfl, ← rep_add, ← rep_add]

theorem mkT_cfg : ∀ (n : Nat) (e : List (Nat × Nat)), (mkT n e).cfg = (Node.t n e).cfg
  | n, (1, c) :: e => by
    show (mkT (n + c + 1) e).cfg = _
    rw [mkT_cfg]
    show (⟨blank, rep (n + c + 1) [false, true] (envT e), .E⟩ : Config) =
      ⟨blank, rep n [false, true] (rep 1 [false] (rep c [true, false] (cons true (envT e)))), .E⟩
    exact congrArg (fun r => (⟨blank, r, .E⟩ : Config)) (t_absorb n c (envT e)).symm
  | _, [] => rfl
  | _, (0, _) :: _ => rfl
  | _, (_ + 2, _) :: _ => rfl

theorem cfg_canon (A B : Nat) (e : List (Nat × Nat)) : (Node.d A B (canon e)).cfg = (Node.d A B e).cfg := by
  simp only [Node.cfg, envT_canon]

/-! ## The map -/

/-- The result of one macro move. -/
inductive Res where
  | next (n : Node)
  | halt
  | stuck
  deriving DecidableEq, Repr

/-- One macro move. `stuck`: no rule of this file covers the node. -/
def F : Node → Res
  | .d (a + 3) b [] => .next (.d (a + 1) (b + 2) [])
  | .d (a + 3) b ((g + 3, c) :: e) => .next (.d (a + 1) (b + 2) ((g + 1, c) :: e))
  | .d (a + 3) b ((1, c + 2) :: e) => .next (.d (a + 1) (b + 3) ((1, c) :: e))
  | .d (a + 3) b [(1, 1)] => .next (.d (a + 1) (b + 3) [])
  | .d (a + 3) b ((1, 1) :: (g + 1, c) :: e) => .next (.d (a + 1) (b + 3) ((g + 1, c) :: e))
  | .d (a + 3) b [(1, 1), (0, c)] => .next (.d (a + 1) (b + c + 4) [])
  | .d (a + 3) b ((1, 1) :: (0, c) :: (g + 1, c') :: e) => .next (.d (a + 1) (b + c + 4) ((g, c') :: e))
  | .d (a + 3) b [(1, 0)] => .next (.p (a + 1) (b + 3) [])
  | .d (a + 3) b ((1, 0) :: (g + 5, c) :: e) => .next (.p (a + 1) (b + 3) ((g, c) :: e))
  | .d (_ + 3) _ ((1, 0) :: (3, _) :: _) => .halt
  | .d (a + 3) b ((1, 0) :: (0, c + 1) :: e) =>
    if b % 2 = 1 then .next (.d 1 0 (canon ((a + 2, b + 2) :: (0, c) :: e)))
    else .next (.d (a + 2) 0 ((2, b + 1) :: (0, c) :: e))
  | .d (a + 3) b [(2, c)] => .next (.d (a + 1) (b + c + 3) [])
  | .d (a + 3) b ((2, c) :: (g + 1, c') :: e) => .next (.d (a + 1) (b + c + 3) ((g, c') :: e))
  | .d (a + 3) b ((2, c) :: (0, d + 2) :: e) => .next (.d (a + 1) (b + c + 4) ((1, d) :: e))
  | .d 2 b [] => .next (.d 1 0 [(1, b + 1)])
  | .d 2 b ((g + 1, c) :: e) => .next (.d 1 0 (canon ((1, b + 1) :: (g, c) :: e)))
  | .d 1 b [] => .next (mkT (b + 3) [])
  | .d 1 b ((g + 1, c) :: e) => .next (mkT (b + 3) ((g, c) :: e))
  | .d 0 b [] => .next (mkT (b + 2) [])
  | .d 0 b ((g + 1, c) :: e) => .next (mkT (b + 2) ((g, c) :: e))
  | .t _ ((2, _) :: _) => .halt
  | .t (n + 1) [] => .next (.d (2 * n + 4) 0 [])
  | .t (n + 1) ((g + 5, c) :: e) => .next (.d (2 * n + 4) 0 ((g + 1, c) :: e))
  | .t (n + 1) ((0, y + 1) :: e) => .next (.d (2 * n + 1) 0 ((1, y) :: e))
  | .p a b [] =>
    if b % 2 = 1 then .next (.d 1 0 [(a + 1, b + 2)])
    else match a with
      | a + 2 => .next (.d (a + 1) (b + 4) [])
      | _ => .stuck
  | .p a b ((g + 5, c) :: e) =>
    if b % 2 = 1 then .next (.d 1 0 (canon ((a + 1, b + 2) :: (g + 2, c) :: e)))
    else match a with
      | a + 2 => .next (.d (a + 1) (b + 4) ((g + 1, c) :: e))
      | _ => .stuck
  | .p a b ((3, c) :: e) =>
    if b % 2 = 1 then .next (.d 1 0 (canon ((a + 1, b + 2) :: (0, c) :: e))) else .stuck
  | .p a b ((4, c) :: e) =>
    if b % 2 = 1 then .next (.d 1 0 (canon ((a + 1, b + 2) :: (1, c) :: e))) else .stuck
  | _ => .stuck

/-- What `F` says about a configuration. -/
def FSem (c : Config) : Res → Prop
  | .next n => Reach c n.cfg
  | .halt => Halts H8002.trans c
  | .stuck => True

theorem odd_of (b : Nat) (h : b % 2 = 1) : ∃ k, b = 2 * k + 1 := ⟨b / 2, by omega⟩
theorem even_of (b : Nat) (h : ¬ b % 2 = 1) : ∃ k, b = 2 * k := ⟨b / 2, by omega⟩

theorem F_sem (n : Node) : FSem n.cfg (F n) := by
  unfold F
  split
  · next a b => exact r_sweep0 a b
  · next a b g c e => exact r_sweep a b g c e
  · next a b c e => exact r_odd a b c e
  · next a b => exact r_oe1' a b
  · next a b g c e => exact r_oe1 a b g c e
  · next a b c => exact r_f1' a b c
  · next a b c g c' e => exact r_f1 a b c g c' e
  · next a b => exact r_oe0' a b
  · next a b g c e => exact r_oe0 a b g c e
  · next a b c e => exact r_tail_halt a b c e
  · next a b c e =>
    split
    · next h =>
      obtain ⟨k, rfl⟩ := odd_of b h
      show Reach _ (Node.d 1 0 (canon _)).cfg
      rw [cfg_canon, show 2 * k + 1 + 2 = 2 * k + 3 by omega]
      exact r_f2o a k c e
    · next h =>
      obtain ⟨k, rfl⟩ := even_of b h
      exact r_f2e a k c e
  · next a b c => exact r_absorb' a b c
  · next a b c g c' e => exact r_absorb a b c g c' e
  · next a b c d e => exact r_f3 a b c d e
  · next b => exact r_end2' b
  · next b g c e =>
    show Reach _ (Node.d 1 0 (canon _)).cfg
    rw [cfg_canon]; exact r_end2 b g c e
  · next b => show Reach _ (mkT _ _).cfg; rw [mkT_cfg]; exact r_end1' b
  · next b g c e => show Reach _ (mkT _ _).cfg; rw [mkT_cfg]; exact r_end1 b g c e
  · next b => show Reach _ (mkT _ _).cfg; rw [mkT_cfg]; exact r_end0' b
  · next b g c e => show Reach _ (mkT _ _).cfg; rw [mkT_cfg]; exact r_end0 b g c e
  · next n c e => exact r_thalt n c e
  · next n => exact r_tblank' n
  · next n g c e => exact r_tblank n g c e
  · next n y e => exact r_tseg n y e
  · next a b =>
    split
    · next h =>
      obtain ⟨k, rfl⟩ := odd_of b h
      show Reach _ (Node.d 1 0 _).cfg
      rw [show 2 * k + 1 + 2 = 2 * k + 3 by omega]
      exact r_podd' a k
    · next h =>
      obtain ⟨k, rfl⟩ := even_of b h
      split
      · next a => exact r_peven' a k
      · trivial
  · next a b g c e =>
    split
    · next h =>
      obtain ⟨k, rfl⟩ := odd_of b h
      show Reach _ (Node.d 1 0 (canon _)).cfg
      rw [cfg_canon, show 2 * k + 1 + 2 = 2 * k + 3 by omega]
      exact r_podd a k (g + 2) c e
    · next h =>
      obtain ⟨k, rfl⟩ := even_of b h
      split
      · next a => exact r_peven a k g c e
      · trivial
  · next a b c e =>
    split
    · next h =>
      obtain ⟨k, rfl⟩ := odd_of b h
      show Reach _ (Node.d 1 0 (canon _)).cfg
      rw [cfg_canon, show 2 * k + 1 + 2 = 2 * k + 3 by omega]
      exact r_podd a k 0 c e
    · trivial
  · next a b c e =>
    split
    · next h =>
      obtain ⟨k, rfl⟩ := odd_of b h
      show Reach _ (Node.d 1 0 (canon _)).cfg
      rw [cfg_canon, show 2 * k + 1 + 2 = 2 * k + 3 by omega]
      exact r_podd a k 1 c e
    · trivial
  · trivial

/-! ## The orbit from blank tape -/

/-- The orbit of the start `d 1 0 []` (S = `1 0 C> 0`, reached from blank tape in 2 steps) under `F`; `halt` and
`stuck` are kept once reached. -/
def adv : Res → Res
  | .next n => F n
  | r => r

/-- `k` moves from `r` (tail recursive, for the evaluation below). -/
def iter : Res → Nat → Res
  | r, 0 => r
  | r, k + 1 => iter (adv r) k

def orbit (k : Nat) : Res := iter (.next (.d 1 0 [])) k

theorem iter_succ : ∀ (k : Nat) (r : Res), iter r (k + 1) = adv (iter r k)
  | 0, _ => rfl
  | k + 1, r => iter_succ k (adv r)

theorem orbit_succ (k : Nat) : orbit (k + 1) = adv (orbit k) := iter_succ k _

theorem start_cfg : steps 2 init = some (Node.d 1 0 []).cfg := by
  rw [start_S]; simp only [Node.cfg, envT, cons_false_blank]

/-- Every node of the orbit is reached from blank tape, after at least as many steps as its index. -/
theorem orbit_reach : ∀ k n, orbit k = .next n → ∃ m, k ≤ m ∧ steps m init = some n.cfg
  | 0, n, h => by
    cases h; exact ⟨2, by omega, start_cfg⟩
  | k + 1, n, h => by
    cases ho : orbit k with
    | next n' =>
      have h' : F n' = .next n := by rw [orbit_succ, ho] at h; exact h
      obtain ⟨m, hm, hs⟩ := orbit_reach k n' ho
      have hr := F_sem n'
      rw [h'] at hr
      obtain ⟨j, hj⟩ := hr
      exact ⟨m + (j + 1), by omega, steps_seq H8002.trans hs hj⟩
    | halt => rw [orbit_succ, ho] at h; cases h
    | stuck => rw [orbit_succ, ho] at h; cases h

/-- **An orbit that reaches `halt` proves that the machine halts from blank tape.** -/
theorem halts_of_orbit : ∀ k, orbit k = .halt → HaltsFromBlank
  | 0, h => by cases h
  | k + 1, h => by
    cases ho : orbit k with
    | next n' =>
      have h' : F n' = .halt := by rw [orbit_succ, ho] at h; exact h
      obtain ⟨m, _, hs⟩ := orbit_reach k n' ho
      have hr := F_sem n'
      rw [h'] at hr
      exact halts_pre ⟨m, hs⟩ hr
    | halt => exact halts_of_orbit k ho
    | stuck => rw [orbit_succ, ho] at h; cases h

/-- **An orbit that never reaches `halt` or `stuck` proves that the machine runs for ever from blank tape.** -/
theorem not_halts_of_orbit (h : ∀ k, ∃ n, orbit k = .next n) : ¬ HaltsFromBlank := by
  refine not_halts_of_forall H8002.trans ?_
  refine forall_of_unbounded H8002.trans (fun m => ∃ c, steps m init = some c) (fun N => ?_) (fun _ h => h)
  obtain ⟨n, hn⟩ := h N
  obtain ⟨m, hm, hs⟩ := orbit_reach N n hn
  exact ⟨m, hm, _, hs⟩

/-- **Main theorem.** If the orbit never gets stuck (every node it meets is covered by a rule of `F`), the machine
halts from blank tape iff the orbit reaches `halt`. -/
theorem halts_iff_of_no_stuck (hs : ∀ k, orbit k ≠ .stuck) : HaltsFromBlank ↔ ∃ k, orbit k = .halt := by
  constructor
  · intro hh
    refine Classical.byContradiction fun hne => not_halts_of_orbit (fun k => ?_) hh
    cases ho : orbit k with
    | next n => exact ⟨n, rfl⟩
    | halt => exact absurd ⟨k, ho⟩ hne
    | stuck => exact absurd ho (hs k)
  · rintro ⟨k, hk⟩; exact halts_of_orbit k hk

/-! ## The orbit, evaluated -/

def Res.isNext : Res → Bool
  | .next _ => true
  | _ => false

theorem orbit_next_of_le {k N : Nat} (hk : k ≤ N) (h : (orbit N).isNext = true) : ∃ n, orbit k = .next n := by
  obtain ⟨d, rfl⟩ : ∃ d, N = k + d := ⟨N - k, by omega⟩
  clear hk
  induction d with
  | zero => cases ho : orbit k with
    | next n => exact ⟨n, rfl⟩
    | halt => rw [Nat.add_zero, ho] at h; cases h
    | stuck => rw [Nat.add_zero, ho] at h; cases h
  | succ d ih =>
    apply ih
    have e : orbit (k + (d + 1)) = adv (orbit (k + d)) := orbit_succ _
    cases ho : orbit (k + d) with
    | next n => rfl
    | halt => rw [e, ho] at h; cases h
    | stuck => rw [e, ho] at h; cases h

set_option maxRecDepth 100000 in
/-- The first 20,000 nodes of the orbit are covered by `F` and do not halt (Lean's kernel). -/
theorem orbit_kernel : ∀ k ≤ 20000, ∃ n, orbit k = .next n :=
  fun _ hk => orbit_next_of_le hk (by decide +kernel)

/-- The first 30,000,000 nodes of the orbit are covered by `F` and do not halt (compiled evaluation). -/
theorem orbit_native : ∀ k ≤ 30000000, ∃ n, orbit k = .next n :=
  fun _ hk => orbit_next_of_le hk (by native_decide)

end H8002
