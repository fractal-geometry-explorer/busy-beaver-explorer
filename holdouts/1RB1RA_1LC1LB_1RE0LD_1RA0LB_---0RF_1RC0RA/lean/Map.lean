import Leaves
import Rules

/-!
# 1RB1RA_1LC1LB_1RE0LD_1RA0LB_---0RF_1RC0RA as a map on lists of block lengths

The tape is always a list of blocks of 1s.  To the left of the head the blocks are separated by one `0`
(`lfin`, nearest block first), to the right by `00` (`rbl`).  Two kinds of configuration:

* `e fs b rest` = `… 0 1^f₂ 0 1^f₁  E> 1^b 00 1^c 00 …`   (state E on the first cell of the block `b`;
  `fs = [f₁, f₂, …]` are the blocks to the left, `rest = [c, …]` the blocks to the right);
* `s fs m rest` = `… 0 1^f₂ 0 1^f₁  B> 0 1^m 00 …`          (state B on the `0` in front of the block `m`).

`G` is the map between them (one block handled per application):

* `e fs 0 rest`        halts (E reads 0);
* `e fs (2j+1) rest` → `e (2 :: inc j fs) (c + j) rest'`      (the block splits: j go left, j go right, the
  odd 1 becomes a finished block `1^2`, and the head goes on to the next block `c`, now `c + j`);
* `e fs (2j+2) rest` → `s (inc j fs) (c + j + 3) rest'`       (an even block: the head turns back);
* `s (f+2 :: fs) m rest` → `s fs f (m+1 :: rest)`             (the way back: each block loses 1, `0` becomes `00`);
* `s (1 :: f :: fs) m rest` → `s fs (f + m + 3) rest`          (a block of one 1 merges its neighbours);
* `s (0 :: fs) m rest`, `s [] m rest` → `e (inc 1 fs) (m+1) rest` (the left end: the next pass starts).

Here `c`, `rest'` are the head and tail of `rest` (0 and `[]` when `rest` is empty), and `inc j` adds `j` to the
first entry of a list (`inc j [] = [j]`).

Main results: `G_sem` (every case of `G` is a run of the machine, of at least one step, or a halt) and
`halts_iff`: **the machine halts from blank tape iff the orbit of `s [] 3 []` under `G` reaches `none`**.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace H139325

open TM

/-! ## Reaching -/

/-- `c` reaches `c'` in at least one step. -/
def Reach (c c' : Config) : Prop := ∃ n, steps (n + 1) c = some c'
/-- `c` reaches `c'` (possibly in no step). -/
def Reaches (c c' : Config) : Prop := ∃ n, steps n c = some c'

theorem Reaches.of {n : Nat} {c c' : Config} (h : steps n c = some c') : Reaches c c' := ⟨n, h⟩
theorem Reach.of {n : Nat} {c c' : Config} (h : steps (n + 1) c = some c') : Reach c c' := ⟨n, h⟩
theorem Reaches.refl (c : Config) : Reaches c c := ⟨0, rfl⟩
theorem Reaches.trans {a b c : Config} : Reaches a b → Reaches b c → Reaches a c
  | ⟨n, h1⟩, ⟨m, h2⟩ => ⟨n + m, steps_seq H139325.trans h1 h2⟩
theorem reach_reaches {a b c : Config} : Reach a b → Reaches b c → Reach a c
  | ⟨n, h1⟩, ⟨m, h2⟩ => ⟨n + m, steps_congr trans (by omega) (steps_seq trans h1 h2)⟩
theorem reaches_reach {a b c : Config} : Reaches a b → Reach b c → Reach a c
  | ⟨n, h1⟩, ⟨m, h2⟩ => ⟨n + m, steps_congr trans (by omega) (steps_seq trans h1 h2)⟩
theorem Reach.reaches {a b : Config} : Reach a b → Reaches a b
  | ⟨n, h⟩ => ⟨n + 1, h⟩
theorem halts_pre {a b : Config} : Reaches a b → Halts trans b → Halts trans a
  | ⟨n, h1⟩, ⟨m, c, h2, h3⟩ => ⟨n + m, c, steps_seq trans h1 h2, h3⟩

/-! ## Tapes of blocks -/

/-- Blocks to the left of the head, nearest first, each followed (going left) by one `0`. -/
def lfin : List Nat → Tape
  | [] => blank
  | f :: fs => rep f [true] (cons false (lfin fs))

/-- Blocks to the right of the head, each followed by `00`. -/
def rbl : List Nat → Tape
  | [] => blank
  | b :: bs => rep b [true] (cons false (cons false (rbl bs)))

/-- Add `j` to the first entry (a new entry if there is none). -/
def inc (j : Nat) : List Nat → List Nat
  | [] => [j]
  | a :: t => (a + j) :: t

theorem ones_add (a b : Nat) (s : Tape) : rep a [true] (rep b [true] s) = rep (a + b) [true] s :=
  (rep_add a b [true] s).symm
theorem one_cons (s : Tape) : cons true s = rep 1 [true] s := rfl
theorem ones_cons (n : Nat) (s : Tape) : rep n [true] (cons true s) = rep (n + 1) [true] s :=
  rep_app_comm n [true] s

theorem lfin_inc (j : Nat) (fs : List Nat) : rep j [true] (lfin fs) = lfin (inc j fs) := by
  cases fs with
  | nil => show rep j [true] blank = rep j [true] (cons false blank); rw [cons_false_blank]
  | cons a t =>
    show rep j [true] (rep a [true] _) = rep (a + j) [true] _
    rw [ones_add, Nat.add_comm]

theorem lfin_ht (fs : List Nat) : lfin fs = rep (fs.headD 0) [true] (cons false (lfin fs.tail)) := by
  cases fs with
  | nil => show blank = cons false blank; rw [cons_false_blank]
  | cons a t => rfl

theorem rbl_ht (bs : List Nat) : rbl bs = rep (bs.headD 0) [true] (cons false (cons false (rbl bs.tail))) := by
  cases bs with
  | nil => show blank = cons false (cons false blank); rw [cons_false_blank, cons_false_blank]
  | cons a t => rfl

theorem rbl_shift (j : Nat) (bs : List Nat) : rep j [true] (rbl bs) = rbl ((bs.headD 0 + j) :: bs.tail) := by
  rw [rbl_ht bs, ones_add, Nat.add_comm]; rfl

/-! ## The configurations -/

inductive Node where
  /-- `lfin fs  E> 1^b 00 rbl rest` -/
  | e (fs : List Nat) (b : Nat) (rest : List Nat)
  /-- `lfin fs  B> 0 1^m 00 rbl rest` -/
  | s (fs : List Nat) (m : Nat) (rest : List Nat)
  deriving DecidableEq, Repr

def Node.cfg : Node → Config
  | .e fs b rest => ⟨lfin fs, rbl (b :: rest), .E⟩
  | .s fs m rest => ⟨lfin fs, cons false (rbl (m :: rest)), .B⟩

/-- The map: one block handled. -/
def G : Node → Option Node
  | .e _ 0 _ => none
  | .e fs (b + 1) rest =>
    if b % 2 = 0 then some (.e (2 :: inc (b / 2) fs) (rest.headD 0 + b / 2) rest.tail)
    else some (.s (inc (b / 2) fs) (rest.headD 0 + b / 2 + 3) rest.tail)
  | .s [] m rest => some (.e [1] (m + 1) rest)
  | .s (0 :: t) m rest => some (.e (inc 1 t) (m + 1) rest)
  | .s (1 :: t) m rest => some (.s t.tail (t.headD 0 + m + 3) rest)
  | .s ((f + 2) :: t) m rest => some (.s t f ((m + 1) :: rest))

/-! ## The rounds: a block gives one 1 to each side per round -/

theorem round1 (n : Nat) (L R : Tape) :
    Reach ⟨L, rep (n + 3) [true] (cons false (cons false R)), .E⟩
      ⟨cons true L, rep (n + 1) [true] (cons false (cons false (cons true R))), .E⟩ := by
  cases n with
  | zero => exact Reach.of (n := 8) (l_three L R)
  | succ n =>
    have h := l_round n L R
    rw [ones_cons, ones_cons] at h
    exact Reach.of (n := 2 * n + 10) h

theorem rounds (j : Nat) : ∀ (b : Nat) (L R : Tape),
    Reaches ⟨L, rep (b + 1 + 2 * j) [true] (cons false (cons false R)), .E⟩
      ⟨rep j [true] L, rep (b + 1) [true] (cons false (cons false (rep j [true] R))), .E⟩ := by
  induction j with
  | zero => intro b L R; exact Reaches.refl _
  | succ j ih =>
    intro b L R
    have h1 := round1 (b + 2 * j) L R
    rw [show b + 2 * j + 3 = b + 1 + 2 * (j + 1) by omega, show b + 2 * j + 1 = b + 1 + 2 * j by omega] at h1
    have h2 := ih b (cons true L) (cons true R)
    rw [ones_cons, ones_cons] at h2
    exact h1.reaches.trans h2

/-! ## Every case of `G` -/

theorem e_odd (fs : List Nat) (j : Nat) (rest : List Nat) :
    Reach (Node.cfg (.e fs (2 * j + 1) rest)) (Node.cfg (.e (2 :: inc j fs) (rest.headD 0 + j) rest.tail)) := by
  have h1 := rounds j 0 (lfin fs) (rbl rest)
  have h2 := l_one (rep j [true] (lfin fs)) (rep j [true] (rbl rest))
  rw [lfin_inc, rbl_shift] at h1 h2
  rw [show 0 + 1 + 2 * j = 2 * j + 1 by omega] at h1
  exact reaches_reach h1 ⟨2, h2⟩

theorem e_even (fs : List Nat) (j : Nat) (rest : List Nat) :
    Reach (Node.cfg (.e fs (2 * j + 2) rest)) (Node.cfg (.s (inc j fs) (rest.headD 0 + j + 3) rest.tail)) := by
  have h1 := rounds j 1 (lfin fs) (rbl rest)
  have h2 := l_two (rep j [true] (lfin fs)) (rep j [true] (rbl rest))
  rw [lfin_inc, rbl_shift] at h1 h2
  rw [show 1 + 1 + 2 * j = 2 * j + 2 by omega] at h1
  exact reaches_reach h1 ⟨9, h2⟩

theorem s_nil (m : Nat) (rest : List Nat) :
    Reach (Node.cfg (.s [] m rest)) (Node.cfg (.e [1] (m + 1) rest)) := by
  have h := l_sw0 blank (rbl (m :: rest))
  rw [cons_false_blank] at h
  refine Reach.of (n := 1) ?_
  show steps 2 ⟨blank, _, _⟩ = some ⟨cons true (cons false blank), _, _⟩
  rw [cons_false_blank]; exact h

theorem s_zero (t : List Nat) (m : Nat) (rest : List Nat) :
    Reach (Node.cfg (.s (0 :: t) m rest)) (Node.cfg (.e (inc 1 t) (m + 1) rest)) := by
  have h := l_sw0 (lfin t) (rbl (m :: rest))
  refine Reach.of (n := 1) ?_
  show steps 2 _ = some ⟨lfin (inc 1 t), _, _⟩
  rw [← lfin_inc]; exact h

theorem s_one (t : List Nat) (m : Nat) (rest : List Nat) :
    Reach (Node.cfg (.s (1 :: t) m rest)) (Node.cfg (.s t.tail (t.headD 0 + m + 3) rest)) := by
  have h1 := l_sw1 (lfin t) (rbl (m :: rest))
  rw [lfin_ht t] at h1
  have h2 := b_left (t.headD 0) (cons false (lfin t.tail)) (cons true (cons true (rbl (m :: rest))))
  have e : cons true (rep (t.headD 0) [true] (cons true (cons true (rbl (m :: rest)))))
      = rbl ((t.headD 0 + m + 3) :: rest) := by
    show _ = rep (t.headD 0 + m + 3) [true] _
    show cons true (rep (t.headD 0) [true] (cons true (cons true (rep m [true] _)))) = _
    simp only [one_cons, ones_add]
    congr 1; omega
  have h3 : steps 1 ⟨cons false (lfin t.tail), cons true (rep (t.headD 0) [true] (cons true (cons true (rbl (m :: rest))))), .B⟩
      = some ⟨lfin t.tail, cons false (rbl ((t.headD 0 + m + 3) :: rest)), .B⟩ := by
    rw [← e]; rfl
  have h := steps_seq trans h1 (steps_seq trans h2 h3)
  rw [← lfin_ht t] at h
  exact Reach.of (n := 5 + (t.headD 0 + 1)) (steps_congr trans (by omega) h)

theorem s_big (f : Nat) (t : List Nat) (m : Nat) (rest : List Nat) :
    Reach (Node.cfg (.s ((f + 2) :: t) m rest)) (Node.cfg (.s t f ((m + 1) :: rest))) := by
  cases f with
  | zero => exact Reach.of (n := 2) (l_sw2 (lfin t) (rbl (m :: rest)))
  | succ f => exact Reach.of (n := f + 3) (l_sw f (lfin t) (rbl (m :: rest)))

theorem e_halt (fs rest : List Nat) : Halts trans (Node.cfg (.e fs 0 rest)) := ⟨0, _, rfl, rfl⟩

/-- What `G` says about the machine: a run of at least one step, or a halt. -/
def GSem (c : Config) : Option Node → Prop
  | none => Halts trans c
  | some s' => Reach c s'.cfg

theorem G_sem (x : Node) : GSem x.cfg (G x) := by
  cases x with
  | e fs b rest =>
    cases b with
    | zero => exact e_halt fs rest
    | succ b =>
      dsimp only [G]
      by_cases hb : b % 2 = 0
      · rw [if_pos hb]
        have h := e_odd fs (b / 2) rest
        rw [show 2 * (b / 2) + 1 = b + 1 by omega] at h
        exact h
      · rw [if_neg hb]
        have h := e_even fs (b / 2) rest
        rw [show 2 * (b / 2) + 2 = b + 1 by omega] at h
        exact h
  | s fs m rest =>
    match fs with
    | [] => exact s_nil m rest
    | 0 :: t => exact s_zero t m rest
    | 1 :: t => exact s_one t m rest
    | (f + 2) :: t => exact s_big f t m rest

/-! ## Halting is the orbit question -/

/-- The orbit of `x` under `G`, `none` once it has hit a halting state. -/
def orbitFrom (x : Node) : Nat → Option Node
  | 0 => some x
  | n + 1 => (G x).bind (fun x' => orbitFrom x' n)

theorem runs_long (N : Nat) : ∀ x : Node, (∀ n, orbitFrom x n ≠ none) →
    ∃ m, N ≤ m ∧ ∃ c, steps m x.cfg = some c := by
  induction N with
  | zero => intro x _; exact ⟨0, Nat.le_refl 0, _, rfl⟩
  | succ N ih =>
    intro x hs
    cases hF : G x with
    | none => exact absurd (by simp [orbitFrom, hF]) (hs 1)
    | some x' =>
      have hs' : ∀ n, orbitFrom x' n ≠ none := fun n h => hs (n + 1) (by simp [orbitFrom, hF, h])
      obtain ⟨m, hm, c, hc⟩ := ih x' hs'
      have hr := G_sem x
      rw [hF] at hr
      obtain ⟨k, hk⟩ := hr
      exact ⟨k + 1 + m, by omega, c, steps_seq trans hk hc⟩

/-- **The machine halts from the configuration `x` iff the orbit of `x` under `G` reaches `none`.** -/
theorem halts_from (x : Node) : Halts trans x.cfg ↔ ∃ n, orbitFrom x n = none := by
  constructor
  · intro hh
    refine Classical.byContradiction fun hne => ?_
    have hs : ∀ n, orbitFrom x n ≠ none := fun n h => hne ⟨n, h⟩
    refine not_halts_of_forall trans ?_ hh
    exact forall_of_unbounded trans (fun m => ∃ c, steps m x.cfg = some c) (runs_long · x hs) (fun _ h => h)
  · rintro ⟨n, hn⟩
    induction n generalizing x with
    | zero => simp [orbitFrom] at hn
    | succ n ih =>
      have hr := G_sem x
      cases hF : G x with
      | none => rw [hF] at hr; exact hr
      | some x' =>
        rw [hF] at hr
        have hn' : orbitFrom x' n = none := by simpa [orbitFrom, hF] using hn
        exact halts_pre hr.reaches (ih x' hn')

/-! ## Where it halts

`G x = none` only for `x = e fs 0 rest`, and that configuration is reached only from `e fs 1 rest` with `rest`
empty or starting with an empty block.  Blocks right of the head are never empty in the run, so the machine halts
exactly when the head, splitting blocks on its way to the right, arrives at the right end of the tape with a last
block of the form `1^(2^k - 1)`: that block is halved (k - 1 times) down to `1`, and then E reads 0. -/

theorem G_none_iff (x : Node) : G x = none ↔ ∃ fs rest, x = .e fs 0 rest := by
  constructor
  · intro h
    match x, h with
    | .e fs 0 rest, _ => exact ⟨fs, rest, rfl⟩
    | .e fs (b + 1) rest, h => dsimp only [G] at h; split at h <;> cases h
    | .s [] m rest, h => cases h
    | .s (0 :: t) m rest, h => cases h
    | .s (1 :: t) m rest, h => cases h
    | .s ((f + 2) :: t) m rest, h => cases h
  · rintro ⟨fs, rest, rfl⟩; rfl

theorem pow_pred (k : Nat) : 2 ^ (k + 1) - 1 = (2 * (2 ^ k - 1)) + 1 := by
  have : 0 < 2 ^ k := Nat.two_pow_pos k
  rw [Nat.pow_succ]; omega

/-- A last block `1^(2^(k+1) - 1)` under the head in E halts: the orbit reaches `none` after `k + 2` applications. -/
theorem last_block_halts (k : Nat) : ∀ fs : List Nat, orbitFrom (.e fs (2 ^ (k + 1) - 1) []) (k + 2) = none := by
  induction k with
  | zero => intro fs; rfl
  | succ k ih =>
    intro fs
    have h : G (.e fs (2 ^ (k + 1 + 1) - 1) []) = some (.e (2 :: inc (2 ^ (k + 1) - 1) fs) (2 ^ (k + 1) - 1) []) := by
      rw [pow_pred (k + 1)]
      dsimp only [G]
      rw [if_pos (by omega)]
      simp
    show (G (.e fs (2 ^ (k + 1 + 1) - 1) [])).bind (fun x' => orbitFrom x' (k + 2)) = none
    rw [h]
    exact ih _


/-- Blank tape reaches `B> 0 1 1 1` in 8 steps. -/
theorem blank_start : steps 8 init = some (Node.cfg (.s [] 3 [])) := by
  show steps 8 init = some (⟨blank, cons false (cons true (cons true (cons true (cons false (cons false blank))))), .B⟩ : Config)
  rw [cons_false_blank, cons_false_blank]
  rfl

theorem steps_add (a b : Nat) : ∀ c : Config, TM.steps trans (a + b) c = (TM.steps trans a c).bind (TM.steps trans b) := by
  induction a with
  | zero => intro c; simp
  | succ a ih =>
    intro c
    rw [show a + 1 + b = (a + b) + 1 by omega]
    cases hs : step c with
    | none => simp [TM.steps, hs]
    | some d => rw [steps_succ_of_step trans (a + b) hs, steps_succ_of_step trans a hs]; exact ih d

/-- A run of `n` steps from `a` to `b` does not change whether the machine halts. -/
theorem halts_congr {n : Nat} {a b : Config} (h : steps n a = some b) : Halts trans a ↔ Halts trans b := by
  constructor
  · rintro ⟨m, c, h1, h2⟩
    by_cases hm : m < n
    · have h3 := steps_halt trans h1 h2 (n - m - 1)
      rw [show m + (n - m - 1 + 1) = n by omega] at h3
      cases h.symm.trans h3
    · have h3 := steps_add n (m - n) a
      rw [show n + (m - n) = m by omega] at h3
      have h4 : TM.steps trans (m - n) b = some c := by
        have h5 : (TM.steps trans n a).bind (TM.steps trans (m - n)) = some c := h3.symm.trans h1
        have h6 : TM.steps trans n a = some b := h
        rw [h6] at h5; exact h5
      exact ⟨m - n, c, h4, h2⟩
  · exact halts_pre (Reaches.of h)

/-- **Main theorem.** The machine halts from blank tape iff the orbit of `s [] 3 []` (`B> 0 1 1 1`, reached
from blank tape in 8 steps) under `G` reaches `none`, i.e. reaches a configuration `e fs 0 rest`. -/
theorem halts_iff : HaltsFromBlank ↔ ∃ n, orbitFrom (.s [] 3 []) n = none := by
  rw [← halts_from]
  exact halts_congr blank_start

end H139325
