import Deal
import TM.MapOrbit

/-! # The event map of 1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF, proved

Written by hand, on the rules of `Rules.lean` and `deals` of `Deal.lean`.

`Lcfg l` is the machine at its left end: the head, in state D, on the blank cell left of the blocks of 1s whose
lengths are the list `l`, single 0s between them.  `visit` is the map of the README ("The event map"): read the
list from the left with a running value `cur = 3j + r`; r = 1 keeps j + 1 and goes on with the next block plus 2j,
r = 2 keeps j - 1 and gives 2j + 5 to the next block, r = 0 keeps j, gives 2j to the next block and 2 to the one
after; the first block gets one more at the end; blocks past the end of the list count as 0.  It answers `none`
when a value after the first is 2, 3 or 5 (or below 2), where the rules do not hold.

`visit_sound`: if `visit f l = some l'` then the machine goes from `Lcfg l` to `Lcfg l'` in one step or more.
`start`: the machine is at `Lcfg [7, 2]` after 66 steps from blank tape.
`not_halts_of_run`: if the map can be applied for ever from `[7, 2]`, the machine does not halt.
`visitHalts_sound`, `halts_of_reach`: where the dealing meets a later value 5 (`[4, 3, ...]`, `[7, 1, ...]`), the
machine halts; so it halts from blank tape if the map from `[7, 2]` reaches such a list.

Not proved here: what the machine does at a later value 2 or 3 (the README's table has it from runs).

The fuel `f` only bounds the number of blocks dealt in one visit; the answer does not depend on it once it is
large enough. -/

namespace H68273

open TM

/-! ## Configurations -/

/-- The first block of a list, 0 if there is none. -/
def hd (l : List Nat) : Nat := l.headD 0

/-- Blocks of 1s with single 0s after each, then blank tape. -/
def blk : List Nat → Tape
  | [] => blank
  | a :: l => rep a [true] (cons false (blk l))

/-- A list of blocks is its first block (0 if none), a 0 and the rest. -/
theorem blk_eq (l : List Nat) : blk l = rep (hd l) [true] (cons false (blk l.tail)) := by
  cases l with
  | nil => simp only [blk, hd, List.headD, List.tail, rep_zero, cons_false_blank]
  | cons a l => rfl

/-- The finished blocks left of the head, nearest first: `0 1^a 0` each. -/
def stk : List Nat → Tape
  | [] => blank
  | a :: s => cons false (rep a [true] (cons false (stk s)))

/-- The left end: `D> 0 1^l0 0 1^l1 0 ...`. -/
def Lcfg (l : List Nat) : Config := ⟨blank, cons false (blk l), .D⟩

/-- The left end with the first two blocks written out. -/
def L0 (a m : Nat) (R : Tape) : Config := ⟨blank, cons false (rep a [true] (cons false (rep m [true] R))), .D⟩

/-- On the way back: `(finished blocks) D> 0 R`. -/
def Dcfg (s : List Nat) (R : Tape) : Config := ⟨stk s, cons false R, .D⟩

/-- Dealing: `(finished blocks) 0 1^(k+1) 000 F> 1^n 0 1^m R`. -/
def Fcfg (s : List Nat) (k n m : Nat) (R : Tape) : Config := dealCfg (cons false (stk s)) R k n m

/-- Between two blocks: `(finished blocks) 0000 1^c 0 C> R`; the block being entered had c + 2 ones. -/
def Ccfg (s : List Nat) (c : Nat) (R : Tape) : Config :=
  ⟨cons false (rep c [true] (cons false (cons false (cons false (cons false (stk s)))))), R, .C⟩

theorem Lcfg_eq (a : Nat) (rest : List Nat) : Lcfg (a :: rest) = L0 a (hd rest) (cons false (blk rest.tail)) := by
  rw [Lcfg, blk, blk_eq rest]; rfl

/-- Equal configurations: unfold, write every 1 as a repeat, join repeats, compare counts with `omega`. -/
macro "tp" : tactic => `(tactic| (simp only [Lcfg, L0, Dcfg, Fcfg, Ccfg, dealCfg, stk, blk, cons_false_blank,
  ones_one, ones_ones, rep_zero] <;> tape_cong))

theorem _root_.TM.Plus.cast {c c' d d' : Config} (h : Plus trans c d) (e₁ : c' = c) (e₂ : d = d') : Plus trans c' d' := by
  subst e₁ e₂; exact h

theorem _root_.TM.Star.cast {c c' d d' : Config} (h : Star trans c d) (e₁ : c' = c) (e₂ : d = d') : Star trans c' d' := by
  subst e₁ e₂; exact h

/-! ## The rules on these configurations -/

theorem L_enter (a m : Nat) (R : Tape) : Plus trans (L0 (a + 1) m R) (Fcfg [] 0 a m R) :=
  plus_of (enter a blank (cons false (rep m [true] R))) (by tp) (by tp)

theorem L_one (b : Nat) (R : Tape) : Plus trans (L0 1 (b + 2) R) (Ccfg [1] b R) :=
  plus_of (one b blank R) (by tp) (by tp)

theorem F_deals (s : List Nat) (k n j m : Nat) (R : Tape) :
    Star trans (Fcfg s k (n + 1 + 3 * j) m R) (Fcfg s (k + j) (n + 1) (m + 2 * j) R) :=
  ⟨_, deals n j (cons false (stk s)) R k m⟩

theorem F_end1 (s : List Nat) (k m : Nat) (R : Tape) : Plus trans (Fcfg s k 3 m R) (Ccfg ((k + 2) :: s) m R) :=
  plus_of (end1c m (rep k [true] (cons false (stk s))) R) (by tp) (by tp)

theorem F_end0 (s : List Nat) (k m p : Nat) (R : Tape) :
    Plus trans (Fcfg s k 2 m (cons false (rep p [true] R)))
      (Dcfg ((k + 1) :: s) (rep (m + 2) [true] (cons false (rep (p + 2) [true] R)))) := by
  match m with
  | 0 => exact plus_of (end0_0 p (rep (k + 1) [true] (cons false (stk s))) R) (by tp) (by tp)
  | 1 => exact plus_of (end0_1 p (rep (k + 1) [true] (cons false (stk s))) R) (by tp) (by tp)
  | 2 => exact plus_of (end0_2 p (rep (k + 1) [true] (cons false (stk s))) R) (by tp) (by tp)
  | m + 3 => exact plus_of (end0_3 m p (rep (k + 1) [true] (cons false (stk s))) R) (by tp) (by tp)

theorem F_end2 (s : List Nat) (k m : Nat) (R : Tape) :
    Plus trans (Fcfg s (k + 1) 1 m R) (Dcfg s (rep (k + 1) [true] (cons false (rep (m + 5) [true] R)))) := by
  match k with
  | 0 => exact plus_of (end2_1 m (stk s) R) (by tp) (by tp)
  | k + 1 => exact plus_of (end2_2 k m (stk s) R) (by tp) (by tp)

theorem F_vanish (m p : Nat) (R : Tape) :
    Plus trans (Fcfg [] 0 1 m (cons false (rep p [true] R)))
      (Dcfg [] (rep (m + 5) [true] (cons false (rep (p + 2) [true] R)))) := by
  match m with
  | 0 => exact plus_of (vanish_0 p blank R) (by tp) (by tp)
  | 1 => exact plus_of (vanish_1 p blank R) (by tp) (by tp)
  | 2 => exact plus_of (vanish_2 p blank R) (by tp) (by tp)
  | m + 3 => exact plus_of (vanish_3 m p blank R) (by tp) (by tp)

theorem C_two (a : Nat) (s : List Nat) (m : Nat) (R : Tape) :
    Plus trans (Ccfg (a :: s) 2 (cons false (rep m [true] R))) (Ccfg (1 :: a :: s) m R) :=
  plus_of (c2 m (rep a [true] (cons false (stk s))) R) (by tp) (by tp)

theorem C_four (a : Nat) (s : List Nat) (n p : Nat) (R : Tape) :
    Plus trans (Ccfg (a :: s) (n + 4) (cons false (rep p [true] R))) (Fcfg (a :: s) 0 (n + 2) (p + 2) R) :=
  plus_of (c4 n p (rep a [true] (cons false (stk s))) R) (by tp) (by tp)

theorem D_sweep (a : Nat) (s : List Nat) (R : Tape) (ha : 0 < a) :
    Plus trans (Dcfg (a :: s) R) (Dcfg s (rep (a + 1) [true] (cons false R))) := by
  match a, ha with
  | 1, _ => exact plus_of (sweep_1 (stk s) R) (by tp) (by tp)
  | b + 2, _ => exact plus_of (sweep_2 b (stk s) R) (by tp) (by tp)

/-- A later block of value 5 (entered with 3 ones left of the head): the machine halts. -/
theorem C_five_halts (a : Nat) (s : List Nat) (p : Nat) (R : Tape) :
    Halts trans (Ccfg ((a + 1) :: s) 3 (cons false (rep p [true] (cons false R)))) := by
  match p with
  | 0 => exact halts_at (five_0 (rep a [true] (cons false (stk s))) R) (by tp) rfl
  | 1 => exact halts_at (five_1 (rep a [true] (cons false (stk s))) R) (by tp) rfl
  | 2 => exact halts_at (five_2 (rep a [true] (cons false (stk s))) R) (by tp) rfl
  | p + 3 => exact halts_at (five_3 p (rep a [true] (cons false (stk s))) R) (by tp) rfl

/-! ## One block, by its remainder

A later block of value `cur` is entered as `Ccfg _ (cur - 2) _`; `i` is `cur / 3 - 2`. -/

/-- A later block of value 3(i + 2) + 1 keeps i + 2 (one more on the way back); the next gets 2(i + 2). -/
theorem C_r1 (a : Nat) (s : List Nat) (i m : Nat) (R : Tape) :
    Plus trans (Ccfg (a :: s) (3 * i + 5) (cons false (rep m [true] R))) (Ccfg ((i + 2) :: a :: s) (m + 2 * i + 2) R) :=
  ((C_four a s (3 * i + 1) m R).cast (by tp) rfl).trans_star
    (((F_deals (a :: s) 0 2 i (m + 2) R).cast (by tp) rfl).trans
      ((F_end1 (a :: s) (0 + i) (m + 2 + 2 * i) R).cast (by tp) (by tp)).star)

/-- A later block of value 3(i + 2) + 2 keeps i + 1; the next gets 2(i + 2) + 5; the head turns back. -/
theorem C_r2 (a : Nat) (s : List Nat) (i m : Nat) (R : Tape) :
    Plus trans (Ccfg (a :: s) (3 * i + 6) (cons false (rep m [true] R)))
      (Dcfg (a :: s) (rep (i + 1) [true] (cons false (rep (m + 2 * i + 9) [true] R)))) :=
  ((C_four a s (3 * i + 2) m R).cast (by tp) rfl).trans_star
    (((F_deals (a :: s) 0 0 (i + 1) (m + 2) R).cast (by tp) rfl).trans
      ((F_end2 (a :: s) i (m + 2 + 2 * (i + 1)) R).cast (by tp) (by tp)).star)

/-- A later block of value 3(i + 2) keeps i + 1 (one more on the way back); the next gets 2(i + 2), the one after 2. -/
theorem C_r0 (a : Nat) (s : List Nat) (i m p : Nat) (R : Tape) :
    Plus trans (Ccfg (a :: s) (3 * i + 4) (cons false (rep m [true] (cons false (rep p [true] R)))))
      (Dcfg ((i + 1) :: a :: s) (rep (m + 2 * i + 4) [true] (cons false (rep (p + 2) [true] R)))) :=
  ((C_four a s (3 * i) m (cons false (rep p [true] R))).cast (by tp) rfl).trans_star
    (((F_deals (a :: s) 0 1 i (m + 2) (cons false (rep p [true] R))).cast (by tp) rfl).trans
      ((F_end0 (a :: s) (0 + i) (m + 2 + 2 * i) p R).cast (by tp) (by tp)).star)

/-- A first block of 3(i + 1) + 1 keeps i + 2 (one more on the way back); the next gets 2(i + 1). -/
theorem A_r1 (i m : Nat) (R : Tape) : Plus trans (L0 (3 * i + 4) m R) (Ccfg [i + 2] (m + 2 * i) R) :=
  ((L_enter (3 * i + 3) m R).cast (by tp) rfl).trans_star
    (((F_deals [] 0 2 i m R).cast (by tp) rfl).trans ((F_end1 [] (0 + i) (m + 2 * i) R).cast (by tp) (by tp)).star)

/-- A first block of 3(i + 1) + 2 keeps i + 1; the next gets 2(i + 1) + 5. -/
theorem A_r2 (i m : Nat) (R : Tape) :
    Plus trans (L0 (3 * i + 5) m R) (Dcfg [] (rep (i + 1) [true] (cons false (rep (m + 2 * i + 7) [true] R)))) :=
  ((L_enter (3 * i + 4) m R).cast (by tp) rfl).trans_star
    (((F_deals [] 0 0 (i + 1) m R).cast (by tp) rfl).trans
      ((F_end2 [] i (m + 2 * (i + 1)) R).cast (by tp) (by tp)).star)

/-- A first block of 3(i + 1) keeps i + 1 (one more on the way back); the next gets 2(i + 1), the one after 2. -/
theorem A_r0 (i m p : Nat) (R : Tape) :
    Plus trans (L0 (3 * i + 3) m (cons false (rep p [true] R)))
      (Dcfg [i + 1] (rep (m + 2 * i + 2) [true] (cons false (rep (p + 2) [true] R)))) :=
  ((L_enter (3 * i + 2) m (cons false (rep p [true] R))).cast (by tp) rfl).trans_star
    (((F_deals [] 0 1 i m (cons false (rep p [true] R))).cast (by tp) rfl).trans
      ((F_end0 [] (0 + i) (m + 2 * i) p R).cast (by tp) (by tp)).star)

/-- A first block of 2 vanishes; the next gets 5, the one after 2. -/
theorem A_two (m p : Nat) (R : Tape) :
    Plus trans (L0 2 m (cons false (rep p [true] R)))
      (Dcfg [] (rep (m + 5) [true] (cons false (rep (p + 2) [true] R)))) :=
  (L_enter 1 m (cons false (rep p [true] R))).trans (F_vanish m p R)

/-! ## The way back -/

/-- The finished blocks `s` (nearest first), each one more, put in front of the list `t`. -/
def unstack : List Nat → List Nat → List Nat
  | [], t => t
  | a :: s, t => unstack s ((a + 1) :: t)

/-- Every block is at least 1. -/
def Pos : List Nat → Prop
  | [] => True
  | a :: s => 0 < a ∧ Pos s

theorem sweep_all : ∀ (s t : List Nat), Pos s → Star trans (Dcfg s (blk t)) (Lcfg (unstack s t))
  | [], _, _ => Star.refl _
  | a :: s, t, h => (D_sweep a s (blk t) h.1).star.trans (sweep_all s ((a + 1) :: t) h.2)

/-! ## The map -/

/-- The blocks after the first: `s` the finished blocks (nearest first, before their last one more), `cur` the
running value, `rest` the blocks not yet reached. -/
def later : Nat → List Nat → Nat → List Nat → Option (List Nat)
  | 0, _, _, _ => none
  | f + 1, s, cur, rest =>
    if cur = 4 then later f (1 :: s) (hd rest + 2) rest.tail
    else if cur < 6 then none
    else if cur % 3 = 1 then later f (cur / 3 :: s) (hd rest + 2 * (cur / 3)) rest.tail
    else if cur % 3 = 2 then some (unstack s ((cur / 3 - 1) :: (hd rest + 2 * (cur / 3) + 5) :: rest.tail))
    else some (unstack ((cur / 3 - 1) :: s) ((hd rest + 2 * (cur / 3)) :: (hd rest.tail + 2) :: rest.tail.tail))

/-- One left-end visit: the event map. `f` bounds the number of blocks dealt. -/
def visit (f : Nat) : List Nat → Option (List Nat)
  | [] => none
  | l0 :: rest =>
    if l0 = 0 then none
    else if l0 = 1 then (if hd rest < 2 then none else later f [1] (hd rest) rest.tail)
    else if l0 = 2 then some ((hd rest + 5) :: (hd rest.tail + 2) :: rest.tail.tail)
    else if l0 % 3 = 1 then later f [l0 / 3 + 1] (hd rest + 2 * (l0 / 3)) rest.tail
    else if l0 % 3 = 2 then some (l0 / 3 :: (hd rest + 2 * (l0 / 3) + 5) :: rest.tail)
    else some (unstack [l0 / 3] ((hd rest + 2 * (l0 / 3)) :: (hd rest.tail + 2) :: rest.tail.tail))

/-- The examples of the README. -/
example : visit 9 [16, 77, 91, 182, 2] = some [7, 29, 149, 184, 2] := by decide
example : visit 9 [100, 123] = some [35, 63, 126, 2] := by decide
example : visit 9 [2, 8, 9] = some [13, 11] := by decide
example : visit 9 [4, 3, 9] = none := by decide

theorem later_sound : ∀ (f a : Nat) (s : List Nat) (cur : Nat) (rest out : List Nat), Pos (a :: s) →
    later f (a :: s) cur rest = some out →
    Plus trans (Ccfg (a :: s) (cur - 2) (cons false (blk rest))) (Lcfg out) := by
  intro f
  induction f with
  | zero => intro a s cur rest out _ h; simp [later] at h
  | succ f ih =>
    intro a s cur rest out hp h
    rw [blk_eq rest]
    simp only [later] at h
    split at h
    · rename_i h4
      subst h4
      exact (C_two a s (hd rest) _).trans
        ((ih 1 (a :: s) (hd rest + 2) rest.tail out ⟨by omega, hp⟩ h).cast (by tp) rfl)
    · split at h
      · cases h
      · split at h
        · rename_i h4 h6 h1
          refine ((C_r1 a s (cur / 3 - 2) (hd rest) _).cast (by tp) rfl).trans ?_
          exact (ih (cur / 3) (a :: s) (hd rest + 2 * (cur / 3)) rest.tail out ⟨by omega, hp⟩ h).cast (by tp) rfl
        · split at h
          · rename_i h4 h6 h1 h2
            cases h
            refine ((C_r2 a s (cur / 3 - 2) (hd rest) _).cast (by tp) rfl).trans_star ?_
            exact (sweep_all (a :: s) _ hp).cast (by tp) rfl
          · rename_i h4 h6 h1 h2
            cases h
            rw [blk_eq rest.tail]
            refine ((C_r0 a s (cur / 3 - 2) (hd rest) (hd rest.tail) _).cast (by tp) rfl).trans_star ?_
            exact (sweep_all ((cur / 3 - 1) :: a :: s) _ ⟨by omega, hp⟩).cast (by tp) rfl

/-- **The event map is what the machine does**: where `visit` answers, the machine goes from the left end with
blocks `l` to the left end with blocks `visit l`, in one step or more. -/
theorem visit_sound {f : Nat} {l out : List Nat} (h : visit f l = some out) : Plus trans (Lcfg l) (Lcfg out) := by
  cases l with
  | nil => simp [visit] at h
  | cons l0 rest =>
    rw [Lcfg_eq]
    simp only [visit] at h
    split at h
    · cases h
    · split at h
      · split at h
        · cases h
        · rename_i h0 h1 h2
          subst h1
          exact ((L_one (hd rest - 2) _).cast (by tp) rfl).trans (later_sound f 1 [] (hd rest) rest.tail out ⟨by omega, trivial⟩ h)
      · split at h
        · rename_i h0 h1 h2
          subst h2
          cases h
          rw [blk_eq rest.tail]
          exact (A_two (hd rest) (hd rest.tail) _).cast rfl (by tp)
        · split at h
          · rename_i h0 h1 h2 h3
            refine ((A_r1 (l0 / 3 - 1) (hd rest) _).cast (by tp) rfl).trans ?_
            exact (later_sound f (l0 / 3 + 1) [] (hd rest + 2 * (l0 / 3)) rest.tail out ⟨by omega, trivial⟩ h).cast
              (by tp) rfl
          · split at h
            · rename_i h0 h1 h2 h3 h4
              cases h
              exact (A_r2 (l0 / 3 - 1) (hd rest) _).cast (by tp) (by tp)
            · rename_i h0 h1 h2 h3 h4
              cases h
              rw [blk_eq rest.tail]
              refine ((A_r0 (l0 / 3 - 1) (hd rest) (hd rest.tail) _).cast (by tp) rfl).trans_star ?_
              exact (sweep_all [l0 / 3] _ ⟨by omega, trivial⟩).cast (by tp) rfl

/-! ## Where the machine halts: a later value 5 -/

/-- The dealing reaches a block with value 5. -/
def laterHalts : Nat → Nat → List Nat → Bool
  | 0, _, _ => false
  | f + 1, cur, rest =>
    if cur = 5 then true
    else if cur = 4 then laterHalts f (hd rest + 2) rest.tail
    else if cur < 6 then false
    else if cur % 3 = 1 then laterHalts f (hd rest + 2 * (cur / 3)) rest.tail
    else false

/-- The visit from the list reaches a later block with value 5: `[4, 3, ...]`, `[7, 1, ...]`, `[4, 2, 3, ...]`, ... -/
def visitHalts (f : Nat) : List Nat → Bool
  | [] => false
  | l0 :: rest =>
    if l0 = 1 then (if hd rest < 2 then false else laterHalts f (hd rest) rest.tail)
    else if l0 < 4 then false
    else if l0 % 3 = 1 then laterHalts f (hd rest + 2 * (l0 / 3)) rest.tail
    else false

example : visitHalts 9 [4, 3, 9] = true := by decide
example : visitHalts 9 [7, 1] = true := by decide
example : visitHalts 9 [4, 2, 3, 100] = true := by decide

theorem laterHalts_sound : ∀ (f a : Nat) (s : List Nat) (cur : Nat) (rest : List Nat), Pos (a :: s) →
    laterHalts f cur rest = true → Halts trans (Ccfg (a :: s) (cur - 2) (cons false (blk rest))) := by
  intro f
  induction f with
  | zero => intro a s cur rest _ h; simp [laterHalts] at h
  | succ f ih =>
    intro a s cur rest hp h
    rw [blk_eq rest]
    simp only [laterHalts] at h
    split at h
    · rename_i h5
      subst h5
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by have := hp.1; omega⟩
      exact C_five_halts b s (hd rest) _
    · split at h
      · rename_i h5 h4
        subst h4
        exact Halts.pre (C_two a s (hd rest) _).star
          (by have := ih 1 (a :: s) (hd rest + 2) rest.tail ⟨by omega, hp⟩ h; exact this)
      · split at h
        · cases h
        · split at h
          · rename_i h5 h4 h6 h1
            refine Halts.pre ((C_r1 a s (cur / 3 - 2) (hd rest) _).cast (by tp) rfl).star ?_
            have := ih (cur / 3) (a :: s) (hd rest + 2 * (cur / 3)) rest.tail ⟨by omega, hp⟩ h
            rw [show hd rest + 2 * (cur / 3) - 2 = hd rest + 2 * (cur / 3 - 2) + 2 from by omega,
              show cur / 3 = cur / 3 - 2 + 2 from by omega] at this
            exact this
          · cases h

/-- **Where `visitHalts` says so, the machine halts.** -/
theorem visitHalts_sound {f : Nat} {l : List Nat} (h : visitHalts f l = true) : Halts trans (Lcfg l) := by
  cases l with
  | nil => simp [visitHalts] at h
  | cons l0 rest =>
    rw [Lcfg_eq]
    simp only [visitHalts] at h
    split at h
    · split at h
      · cases h
      · rename_i h1 h2
        subst h1
        exact Halts.pre ((L_one (hd rest - 2) _).cast (by tp) rfl).star
          (laterHalts_sound f 1 [] (hd rest) rest.tail ⟨by omega, trivial⟩ h)
    · split at h
      · cases h
      · split at h
        · rename_i h1 h4 h3
          refine Halts.pre ((A_r1 (l0 / 3 - 1) (hd rest) _).cast (by tp) rfl).star ?_
          have := laterHalts_sound f (l0 / 3 + 1) [] (hd rest + 2 * (l0 / 3)) rest.tail ⟨by omega, trivial⟩ h
          rw [show hd rest + 2 * (l0 / 3) - 2 = hd rest + 2 * (l0 / 3 - 1) from by omega,
            show l0 / 3 + 1 = l0 / 3 - 1 + 2 from by omega] at this
          exact this
        · cases h

/-! ## From blank tape -/

/-- From blank tape the machine is at the left end with blocks 7 and 2 after 66 steps. -/
theorem start : steps 66 init = some (Lcfg [7, 2]) := by
  have h := blank_reaches trans (q := St.A) (n := 66)
    (c := ⟨[], [false, true, true, true, true, true, true, true, false, true, true], .D⟩) (by decide)
  refine h.trans (congrArg some ?_)
  simp only [FCfg.toCfg, Lcfg, blk, app_cons, app_nil, cons_false_blank, ones_one, ones_ones]

/-- A run of the map from `[7, 2]` that never stops: the lists it goes through. -/
def MapRun (seq : Nat → List Nat) : Prop := seq 0 = [7, 2] ∧ ∀ n, ∃ f, visit f (seq n) = some (seq (n + 1))

theorem reach {seq : Nat → List Nat} (h : MapRun seq) : ∀ n, ∃ t, n ≤ t ∧ steps t init = some (Lcfg (seq n))
  | 0 => ⟨66, by omega, by rw [h.1]; exact start⟩
  | n + 1 => by
    obtain ⟨t, ht, hs⟩ := reach h n
    obtain ⟨f, hf⟩ := h.2 n
    obtain ⟨k, hk⟩ := visit_sound hf
    exact ⟨t + (k + 1), by omega, steps_seq trans hs hk⟩

/-- **If the event map can be applied for ever from `[7, 2]`, the machine does not halt.** -/
theorem not_halts_of_run {seq : Nat → List Nat} (h : MapRun seq) : ¬ HaltsFromBlank :=
  not_halts_of_forall trans (forall_of_unbounded trans (fun m => ∃ c, steps m init = some c)
    (fun n => let ⟨t, ht, hs⟩ := reach h n; ⟨t, ht, _, hs⟩) (fun _ hm => hm))

/-- The lists the map goes through from `[7, 2]`. -/
inductive MapReach : List Nat → Prop
  | start : MapReach [7, 2]
  | step {f : Nat} {l l' : List Nat} : MapReach l → visit f l = some l' → MapReach l'

theorem MapReach.star {l : List Nat} (h : MapReach l) : Star trans init (Lcfg l) := by
  induction h with
  | start => exact ⟨66, H68273.start⟩
  | step _ hv ih => exact ih.trans (visit_sound hv).star

/-- **If the map from `[7, 2]` reaches a list where the dealing meets a value 5, the machine halts.** -/
theorem halts_of_reach {f : Nat} {l : List Nat} (h : MapReach l) (hh : visitHalts f l = true) : HaltsFromBlank :=
  Halts.pre h.star (visitHalts_sound hh)

end H68273
