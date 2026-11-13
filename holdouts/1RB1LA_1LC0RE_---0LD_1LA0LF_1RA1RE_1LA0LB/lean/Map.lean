import Rules

/-!
# 1RB1LA_1LC0RE_---0LD_1LA0LF_1RA1RE_1LA0LB as a map on two lists of block lengths

At the moments the head is in state B on a `0` with a block of 1s directly to its left, the tape is

    … 0 1^g₂ 0 1^g₁  B> 0  1^b₀ 000 1^b₁ 000 …

blocks separated by one `0` on the left (`gs = [g₁, g₂, …]`, nearest first) and by `000` on the right
(`bs = [b₀, b₁, …]`; `b₀` may be 0).  Call this configuration `v gs bs`.  `G` is the map from one such moment to
the next, by the length `k = g₁` of the block next to the head (`g` = the block after it, `b` = `b₀`, both 0 if
absent; `inc j` adds `j` to the first entry of a list, `inc j [] = [j]`):

* `k = 0`, or no block on the left: the machine halts (B writes 1, C reads 0);
* `k = 1`:  `v (1 :: g :: gs) (b :: bs) → v ((g + b + 3) :: inc 2 gs) bs`     (three blocks merge);
* `k = 2`:  `v (2 :: g :: gs) (b :: bs) → v ((b + 2) :: (g + 2) :: inc 1 gs) bs`;
* `k = 3`:  `v (3 :: gs) bs → v gs (0 :: inc 1 bs)`                             (the block is erased; one 1 goes right);
* `k ≥ 4`:  `v (k :: gs) (b :: bs) → v ((b + 3) :: (k − 2) :: inc 1 gs) bs`.

Blocks on the left are never 0 (every rule pushes blocks ≥ 2), so the machine halts exactly when the left list is
used up: when a run of blocks `1^3` reaches the left end.

Main results: `G_sem` (every case of `G` is a run of the machine of at least one step, or a halt) and `halts_iff`:
**the machine halts from blank tape iff the orbit of `v [1] []` under `G` reaches `none`.**
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace H52677

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
  | ⟨n, h1⟩, ⟨m, h2⟩ => ⟨n + m, steps_seq H52677.trans h1 h2⟩
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

/-- Blocks to the right of the head, each followed by `000`. -/
def rbl : List Nat → Tape
  | [] => blank
  | b :: bs => rep b [true] (cons false (cons false (cons false (rbl bs))))

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

theorem rbl_ht (bs : List Nat) :
    rbl bs = rep (bs.headD 0) [true] (cons false (cons false (cons false (rbl bs.tail)))) := by
  cases bs with
  | nil => show blank = cons false (cons false (cons false blank)); rw [cons_false_blank, cons_false_blank, cons_false_blank]
  | cons a t => rfl

theorem rbl_inc (j : Nat) (bs : List Nat) : rep j [true] (rbl bs) = rbl (inc j bs) := by
  cases bs with
  | nil =>
    show rep j [true] blank = rep j [true] (cons false (cons false (cons false blank)))
    rw [cons_false_blank, cons_false_blank, cons_false_blank]
  | cons a t =>
    show rep j [true] (rep a [true] _) = rep (a + j) [true] _
    rw [ones_add, Nat.add_comm]

/-! ## The configurations -/

inductive Node where
  /-- `lfin gs  B> 0 rbl bs` -/
  | v (gs : List Nat) (bs : List Nat)
  deriving DecidableEq, Repr

def Node.cfg : Node → Config
  | .v gs bs => ⟨lfin gs, cons false (rbl bs), .B⟩

/-- The map. -/
def G : Node → Option Node
  | .v [] _ => none
  | .v (0 :: _) _ => none
  | .v (1 :: t) bs => some (.v ((t.headD 0 + bs.headD 0 + 3) :: inc 2 t.tail) bs.tail)
  | .v (2 :: t) bs => some (.v ((bs.headD 0 + 2) :: (t.headD 0 + 2) :: inc 1 t.tail) bs.tail)
  | .v (3 :: t) bs => some (.v t (0 :: inc 1 bs))
  | .v ((k + 4) :: t) bs => some (.v ((bs.headD 0 + 3) :: (k + 2) :: inc 1 t) bs.tail)

/-! ## Gadgets (any tape `L`, `R` around them) -/

/-- A runs left over `1^g` and stops on the `0` before it. -/
theorem al (g : Nat) (L R : Tape) :
    steps (g + 1) ⟨rep g [true] (cons false L), cons true R, .A⟩ = some ⟨L, cons false (rep (g + 1) [true] R), .A⟩ := by
  have h1 := a_left g (cons false L) R
  have h2 : steps 1 ⟨cons false L, cons true (rep g [true] R), .A⟩ = some ⟨L, cons false (rep (g + 1) [true] R), .A⟩ := rfl
  exact steps_seq trans h1 h2

/-- F on a `0` writes 1 and A runs left over the block `1^g` to the `0` before it. -/
theorem enterF (g : Nat) (L R : Tape) :
    steps (g + 1) ⟨rep g [true] (cons false L), cons false R, .F⟩ = some ⟨L, cons false (rep (g + 1) [true] R), .A⟩ := by
  cases g with
  | zero => rfl
  | succ g =>
    have h1 : steps 1 ⟨rep (g + 1) [true] (cons false L), cons false R, .F⟩
        = some ⟨rep g [true] (cons false L), cons true (cons true R), .A⟩ := rfl
    have h2 := al g L (cons true R)
    rw [ones_cons] at h2
    exact steps_congr trans (by omega) (steps_seq trans h1 h2)

/-- The same for D. -/
theorem enterD (g : Nat) (L R : Tape) :
    steps (g + 1) ⟨rep g [true] (cons false L), cons false R, .D⟩ = some ⟨L, cons false (rep (g + 1) [true] R), .A⟩ := by
  cases g with
  | zero => rfl
  | succ g =>
    have h1 : steps 1 ⟨rep (g + 1) [true] (cons false L), cons false R, .D⟩
        = some ⟨rep g [true] (cons false L), cons true (cons true R), .A⟩ := rfl
    have h2 := al g L (cons true R)
    rw [ones_cons] at h2
    exact steps_congr trans (by omega) (steps_seq trans h1 h2)

/-- `L A> 0 1^(n+1) R` becomes `L 1 0 1^n E> R`. -/
theorem bounce (n : Nat) (L R : Tape) :
    steps (n + 2) ⟨L, cons false (rep (n + 1) [true] R), .A⟩ = some ⟨rep n [true] (cons false (cons true L)), R, .E⟩ := by
  have h1 : steps 2 ⟨L, cons false (rep (n + 1) [true] R), .A⟩ = some ⟨cons false (cons true L), rep n [true] R, .E⟩ := rfl
  have h2 := e_right n (cons false (cons true L)) R
  exact steps_congr trans (by omega) (steps_seq trans h1 h2)

/-- `L A> 0 1^(n+1) 00 1^(m+1) 000 R` becomes `L 1 0 1^(n+2) 0 1^(m+2) B> 0 R`. -/
theorem z_to_v (n m : Nat) (L R : Tape) :
    Reach ⟨L, cons false (rep (n + 1) [true] (cons false (cons false (rep (m + 1) [true] (cons false (cons false (cons false R))))))), .A⟩
      ⟨rep (m + 2) [true] (cons false (rep (n + 2) [true] (cons false (cons true L)))), cons false R, .B⟩ := by
  have h1 := bounce n L (cons false (cons false (rep (m + 1) [true] (cons false (cons false (cons false R))))))
  have h2 : steps 3 ⟨rep n [true] (cons false (cons true L)), cons false (cons false (rep (m + 1) [true] (cons false (cons false (cons false R))))), .E⟩
      = some ⟨cons false (cons true (cons true (rep n [true] (cons false (cons true L))))), rep m [true] (cons false (cons false (cons false R))), .E⟩ := rfl
  have h3 := e_right m (cons false (cons true (cons true (rep n [true] (cons false (cons true L)))))) (cons false (cons false (cons false R)))
  have h4 : steps 2 ⟨rep m [true] (cons false (cons true (cons true (rep n [true] (cons false (cons true L)))))), cons false (cons false (cons false R)), .E⟩
      = some ⟨cons true (cons true (rep m [true] (cons false (cons true (cons true (rep n [true] (cons false (cons true L)))))))), cons false R, .B⟩ := rfl
  exact ⟨n + 1 + 3 + m + 2, steps_congr trans (by omega) (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4)))⟩

/-! ## Every case of `G` -/

theorem rbl_one (bs : List Nat) :
    cons true (rbl bs) = rep (bs.headD 0 + 1) [true] (cons false (cons false (cons false (rbl bs.tail)))) := by
  rw [rbl_ht bs]; rfl

theorem v_big (k : Nat) (t bs : List Nat) :
    Reach (Node.cfg (.v ((k + 4) :: t) bs)) (Node.cfg (.v ((bs.headD 0 + 3) :: (k + 2) :: inc 1 t) bs.tail)) := by
  have h1 : steps 10 ⟨cons true (cons true (cons true (cons true (rep k [true] (cons false (lfin t)))))), cons false (rbl bs), .B⟩
      = some ⟨rep k [true] (cons false (lfin t)), cons false (cons false (cons false (cons true
          (rep (bs.headD 0 + 1) [true] (cons false (cons false (cons false (rbl bs.tail)))))))), .F⟩ := by
    rw [← rbl_one]; rfl
  have h2 := enterF k (lfin t) (cons false (cons false (cons true
          (rep (bs.headD 0 + 1) [true] (cons false (cons false (cons false (rbl bs.tail))))))))
  have h3 := z_to_v k (bs.headD 0 + 1) (lfin t) (rbl bs.tail)
  have e : cons true (lfin t) = lfin (inc 1 t) := lfin_inc 1 t
  rw [e] at h3
  exact reaches_reach (Reaches.of (steps_seq trans h1 h2)) h3

theorem v_two (t bs : List Nat) :
    Reach (Node.cfg (.v (2 :: t) bs)) (Node.cfg (.v ((bs.headD 0 + 2) :: (t.headD 0 + 2) :: inc 1 t.tail) bs.tail)) := by
  have h1 : steps 3 ⟨cons true (cons true (cons false (lfin t))), cons false (rbl bs), .B⟩
      = some ⟨rep (t.headD 0) [true] (cons false (lfin t.tail)), cons false (cons false (cons false
          (rep (bs.headD 0 + 1) [true] (cons false (cons false (cons false (rbl bs.tail))))))), .F⟩ := by
    rw [← rbl_one, ← lfin_ht]; rfl
  have h2 := enterF (t.headD 0) (lfin t.tail) (cons false (cons false
          (rep (bs.headD 0 + 1) [true] (cons false (cons false (cons false (rbl bs.tail)))))))
  have h3 := z_to_v (t.headD 0) (bs.headD 0) (lfin t.tail) (rbl bs.tail)
  have e : cons true (lfin t.tail) = lfin (inc 1 t.tail) := lfin_inc 1 t.tail
  rw [e] at h3
  exact reaches_reach (Reaches.of (steps_seq trans h1 h2)) h3

theorem v_three (t bs : List Nat) :
    Reach (Node.cfg (.v (3 :: t) bs)) (Node.cfg (.v t (0 :: inc 1 bs))) := by
  refine ⟨3, ?_⟩
  show steps 4 _ = some ⟨lfin t, cons false (cons false (cons false (cons false (rbl (inc 1 bs))))), .B⟩
  rw [← rbl_inc]
  rfl

theorem v_one (t bs : List Nat) :
    Reach (Node.cfg (.v (1 :: t) bs)) (Node.cfg (.v ((t.headD 0 + bs.headD 0 + 3) :: inc 2 t.tail) bs.tail)) := by
  have h1 : steps 2 ⟨cons true (cons false (lfin t)), cons false (rbl bs), .B⟩
      = some ⟨rep (t.headD 0) [true] (cons false (lfin t.tail)), cons false (cons false (cons true (rbl bs))), .D⟩ := by
    rw [← lfin_ht]; rfl
  have h2 := enterD (t.headD 0) (lfin t.tail) (cons false (cons true (rbl bs)))
  have h3 := bounce (t.headD 0) (lfin t.tail) (cons false (cons true (rbl bs)))
  have h4 : steps 2 ⟨rep (t.headD 0) [true] (cons false (cons true (lfin t.tail))), cons false (cons true (rbl bs)), .E⟩
      = some ⟨rep (t.headD 0) [true] (cons false (cons true (lfin t.tail))), cons true (cons true (rbl bs)), .A⟩ := by
    cases t.headD 0 <;> rfl
  have h5 := al (t.headD 0) (cons true (lfin t.tail)) (cons true (rbl bs))
  have e : rep (t.headD 0 + 1) [true] (cons true (rbl bs))
      = rep (t.headD 0 + bs.headD 0 + 1 + 1) [true] (cons false (cons false (cons false (rbl bs.tail)))) := by
    rw [rbl_one, ones_add]; congr 1; omega
  rw [e] at h5
  have h6 := bounce (t.headD 0 + bs.headD 0 + 1) (cons true (lfin t.tail)) (cons false (cons false (cons false (rbl bs.tail))))
  have h7 : steps 2 ⟨rep (t.headD 0 + bs.headD 0 + 1) [true] (cons false (cons true (cons true (lfin t.tail)))), cons false (cons false (cons false (rbl bs.tail))), .E⟩
      = some ⟨cons true (cons true (rep (t.headD 0 + bs.headD 0 + 1) [true] (cons false (cons true (cons true (lfin t.tail)))))), cons false (rbl bs.tail), .B⟩ := rfl
  have h := steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (steps_seq trans h6 h7)))))
  have e2 : cons true (cons true (lfin t.tail)) = lfin (inc 2 t.tail) := lfin_inc 2 t.tail
  rw [e2] at h
  exact ⟨_, steps_congr trans (by omega : _ = (2 + (t.headD 0 + 1 + (t.headD 0 + 2 + (2 + (t.headD 0 + 1 + (t.headD 0 + bs.headD 0 + 1 + 2 + 1))))) + 1)) h⟩

theorem v_halt_nil (bs : List Nat) : Halts trans (Node.cfg (.v [] bs)) := ⟨1, _, rfl, rfl⟩
theorem v_halt_zero (t bs : List Nat) : Halts trans (Node.cfg (.v (0 :: t) bs)) := ⟨1, _, rfl, rfl⟩

/-- What `G` says about the machine: a run of at least one step, or a halt. -/
def GSem (c : Config) : Option Node → Prop
  | none => Halts trans c
  | some s' => Reach c s'.cfg

theorem G_sem (x : Node) : GSem x.cfg (G x) := by
  cases x with
  | v gs bs =>
    match gs with
    | [] => exact v_halt_nil bs
    | 0 :: t => exact v_halt_zero t bs
    | 1 :: t => exact v_one t bs
    | 2 :: t => exact v_two t bs
    | 3 :: t => exact v_three t bs
    | (k + 4) :: t => exact v_big k t bs

/-! ## The transfer loop, done at once

When the block next to the head has `K ≥ 4` ones and the first block on the right is empty (`b = 0`), two
applications of `G` give `v (K :: t) (0 :: bs) → v (3 :: (K-2) :: inc 1 t) bs → v ((K-2) :: inc 1 t) (0 :: inc 1 bs)`:
the block loses two 1s, one goes to the next block on the left and one to the next block on the right, and the
situation repeats.  So the block is dismantled down to 2 (K even) or 3 (K odd) ones, half of it going to each side.
`GA` is `G` with this loop done in one application. -/

theorem inc_inc (a b : Nat) (l : List Nat) : inc a (inc b l) = inc (b + a) l := by
  cases l with
  | nil => rfl
  | cons x t => show (x + b + a) :: t = (x + (b + a)) :: t; rw [Nat.add_assoc]

theorem round (k : Nat) (t bs : List Nat) (hb : bs.headD 0 = 0) :
    Reach (Node.cfg (.v ((k + 4) :: t) bs)) (Node.cfg (.v ((k + 2) :: inc 1 t) (0 :: inc 1 bs.tail))) := by
  have h1 := v_big k t bs
  rw [hb] at h1
  exact reach_reaches h1 (v_three ((k + 2) :: inc 1 t) bs.tail).reaches

theorem loop (j : Nat) : ∀ (k : Nat) (t bs : List Nat), bs.headD 0 = 0 →
    Reach (Node.cfg (.v ((k + 2 + 2 * (j + 1)) :: t) bs)) (Node.cfg (.v ((k + 2) :: inc (j + 1) t) (0 :: inc (j + 1) bs.tail))) := by
  induction j with
  | zero => intro k t bs hb; exact round k t bs hb
  | succ j ih =>
    intro k t bs hb
    have h1 := round (k + 2 * (j + 1)) t bs hb
    rw [show k + 2 * (j + 1) + 4 = k + 2 + 2 * (j + 1 + 1) by omega,
      show k + 2 * (j + 1) + 2 = k + 2 + 2 * (j + 1) by omega] at h1
    have h2 := ih k (inc 1 t) (0 :: inc 1 bs.tail) rfl
    rw [inc_inc] at h2
    have e : (0 :: inc 1 bs.tail).tail = inc 1 bs.tail := rfl
    rw [e, inc_inc, Nat.add_comm 1 (j + 1)] at h2
    exact reach_reaches h1 h2.reaches

/-- `G` with the transfer loop done at once. -/
def GA : Node → Option Node
  | .v ((k + 4) :: t) bs =>
    if bs.headD 0 = 0 then some (.v ((2 + k % 2) :: inc (k / 2 + 1) t) (0 :: inc (k / 2 + 1) bs.tail))
    else G (.v ((k + 4) :: t) bs)
  | x => G x

theorem GA_sem (x : Node) : GSem x.cfg (GA x) := by
  cases x with
  | v gs bs =>
    match gs with
    | [] => exact v_halt_nil bs
    | 0 :: t => exact v_halt_zero t bs
    | 1 :: t => exact v_one t bs
    | 2 :: t => exact v_two t bs
    | 3 :: t => exact v_three t bs
    | (k + 4) :: t =>
      dsimp only [GA]
      by_cases hb : bs.headD 0 = 0
      · rw [if_pos hb]
        have h := loop (k / 2) (k % 2) t bs hb
        rw [show k % 2 + 2 + 2 * (k / 2 + 1) = k + 4 by omega, show k % 2 + 2 = 2 + k % 2 by omega] at h
        exact h
      · rw [if_neg hb]; exact v_big k t bs

/-! ## Halting is the orbit question -/

/-- The orbit of `x` under a map `F`, `none` once it has hit a halting state. -/
def orbitOf (F : Node → Option Node) (x : Node) : Nat → Option Node
  | 0 => some x
  | n + 1 => (F x).bind (fun x' => orbitOf F x' n)

/-- The orbit under `G`. -/
abbrev orbitFrom := orbitOf G
/-- The orbit under `GA`. -/
abbrev orbitA := orbitOf GA

section
variable (F : Node → Option Node) (hF : ∀ x, GSem x.cfg (F x))
include hF

theorem runs_long (N : Nat) : ∀ x : Node, (∀ n, orbitOf F x n ≠ none) →
    ∃ m, N ≤ m ∧ ∃ c, steps m x.cfg = some c := by
  induction N with
  | zero => intro x _; exact ⟨0, Nat.le_refl 0, _, rfl⟩
  | succ N ih =>
    intro x hs
    cases hx : F x with
    | none => exact absurd (by simp [orbitOf, hx]) (hs 1)
    | some x' =>
      have hs' : ∀ n, orbitOf F x' n ≠ none := fun n h => hs (n + 1) (by simp [orbitOf, hx, h])
      obtain ⟨m, hm, c, hc⟩ := ih x' hs'
      have hr := hF x
      rw [hx] at hr
      obtain ⟨k, hk⟩ := hr
      exact ⟨k + 1 + m, by omega, c, steps_seq trans hk hc⟩

/-- The machine halts from the configuration `x` iff the orbit of `x` under `F` reaches `none`. -/
theorem halts_from (x : Node) : Halts trans x.cfg ↔ ∃ n, orbitOf F x n = none := by
  constructor
  · intro hh
    refine Classical.byContradiction fun hne => ?_
    have hs : ∀ n, orbitOf F x n ≠ none := fun n h => hne ⟨n, h⟩
    refine not_halts_of_forall trans ?_ hh
    exact forall_of_unbounded trans (fun m => ∃ c, steps m x.cfg = some c) (runs_long F hF · x hs) (fun _ h => h)
  · rintro ⟨n, hn⟩
    induction n generalizing x with
    | zero => simp [orbitOf] at hn
    | succ n ih =>
      have hr := hF x
      cases hx : F x with
      | none => rw [hx] at hr; exact hr
      | some x' =>
        rw [hx] at hr
        have hn' : orbitOf F x' n = none := by simpa [orbitOf, hx] using hn
        exact halts_pre hr.reaches (ih x' hn')

end

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

/-- Blank tape reaches `1 B> 0` in one step. -/
theorem blank_start : steps 1 init = some (Node.cfg (.v [1] [])) := by
  show steps 1 init = some (⟨cons true (cons false blank), cons false blank, .B⟩ : Config)
  rw [cons_false_blank]
  rfl

/-- **Main theorem.** The machine halts from blank tape iff the orbit of `v [1] []` (`1 B> 0`, the configuration
after the first step) under `G` reaches `none`, i.e. reaches a configuration with no block left of the head. -/
theorem halts_iff : HaltsFromBlank ↔ ∃ n, orbitFrom (.v [1] []) n = none := by
  rw [← halts_from G G_sem]
  exact halts_congr blank_start

/-- The same for the map `GA` (the transfer loop done at once), which is much faster to iterate. -/
theorem halts_iff_fast : HaltsFromBlank ↔ ∃ n, orbitA (.v [1] []) n = none := by
  rw [← halts_from GA GA_sem]
  exact halts_congr blank_start

/-! ## Where it halts

`G x = none` only when there is no block left of the head (blocks on the left are never empty in the run: every
rule pushes blocks of at least 2).  The left list is used up exactly when the head, alone with one block `1^x` at
the left end and an empty block on its right, finds `x = 3·(2^m − 1)` (3, 9, 21, 45, …): the transfer loop turns
`x = 2j + 3` into `j`, so `x + 3` is halved again and again, and `x = 3` is erased, leaving nothing. -/

/-- `G` is undefined exactly on the configurations with no block, or an empty block, left of the head. -/
theorem G_none_iff (x : Node) : G x = none ↔ ∃ bs, x = .v [] bs ∨ ∃ t, x = .v (0 :: t) bs := by
  constructor
  · intro h
    match x, h with
    | .v [] bs, _ => exact ⟨bs, Or.inl rfl⟩
    | .v (0 :: t) bs, _ => exact ⟨bs, Or.inr ⟨t, rfl⟩⟩
    | .v (1 :: t) bs, h => cases h
    | .v (2 :: t) bs, h => cases h
    | .v (3 :: t) bs, h => cases h
    | .v ((k + 4) :: t) bs, h => cases h
  · rintro ⟨bs, rfl | ⟨t, rfl⟩⟩ <;> rfl

theorem orbit_add (F : Node → Option Node) (a b : Nat) : ∀ x : Node,
    orbitOf F x (a + b) = (orbitOf F x a).bind (fun y => orbitOf F y b) := by
  induction a with
  | zero => intro x; simp [orbitOf]
  | succ a ih =>
    intro x
    rw [show a + 1 + b = (a + b) + 1 by omega]
    show (F x).bind (fun x' => orbitOf F x' (a + b)) = ((F x).bind (fun x' => orbitOf F x' a)).bind _
    cases F x with
    | none => rfl
    | some x' => exact ih x'

/-- One block `1^(2j+5)` alone at the left end, an empty block on the right: two applications of `GA` leave the
block `1^(j+1)` alone at the left end, again with an empty block on the right. -/
theorem bottom_step (j c : Nat) (bs : List Nat) :
    orbitA (.v [2 * j + 5] (0 :: c :: bs)) 2 = some (.v [j + 1] (0 :: 1 :: (c + (j + 1)) :: bs)) := by
  have h1 : GA (.v [2 * j + 5] (0 :: c :: bs)) = some (.v [3, j + 1] (0 :: (c + (j + 1)) :: bs)) := by
    show GA (.v [(2 * j + 1) + 4] (0 :: c :: bs)) = _
    dsimp only [GA]
    rw [if_pos (show (0 :: c :: bs).headD 0 = 0 from rfl)]
    have e1 : (2 * j + 1) % 2 = 1 := by omega
    have e2 : (2 * j + 1) / 2 = j := by omega
    rw [e1, e2]; rfl
  show (GA (.v [2 * j + 5] (0 :: c :: bs))).bind (fun x' => orbitA x' 1) = _
  rw [h1]
  simp [orbitOf, GA, G, inc]

theorem three_pow (m : Nat) : 3 * (2 ^ (m + 1 + 1) - 1) = 2 * (3 * (2 ^ (m + 1) - 1) - 1) + 5 := by
  have : 0 < 2 ^ m := Nat.two_pow_pos m
  rw [Nat.pow_succ, Nat.pow_succ]; omega

/-- A single block of `3·(2^(m+1) − 1)` ones at the left end, with an empty block on its right, halts. -/
theorem bottom_halts (m : Nat) : ∀ (c : Nat) (bs : List Nat),
    orbitA (.v [3 * (2 ^ (m + 1) - 1)] (0 :: c :: bs)) (2 * m + 2) = none := by
  induction m with
  | zero => intro c bs; rfl
  | succ m ih =>
    intro c bs
    have h := bottom_step (3 * (2 ^ (m + 1) - 1) - 1) c bs
    rw [← three_pow m] at h
    have e : 3 * (2 ^ (m + 1) - 1) - 1 + 1 = 3 * (2 ^ (m + 1) - 1) := by
      have : 0 < 2 ^ m := Nat.two_pow_pos m
      rw [Nat.pow_succ]; omega
    rw [e] at h
    have ha := orbit_add GA 2 (2 * m + 2) (.v [3 * (2 ^ (m + 1 + 1) - 1)] (0 :: c :: bs))
    rw [show 2 * (m + 1) + 2 = 2 + (2 * m + 2) by omega]
    show orbitOf GA _ (2 + (2 * m + 2)) = none
    have h' : orbitOf GA (.v [3 * (2 ^ (m + 1 + 1) - 1)] (0 :: c :: bs)) 2 = _ := h
    rw [ha, h']
    exact ih _ _

end H52677
