import EventRules

/-!
# 1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB: the event map

The tape is written by run lengths.  One side of the head is a list of pairs `(g, b)`, nearest the head first:
`g` zeros, then `b` ones (`dec`); beyond the list the tape is blank.  A state `RS` is the left list, the machine
state and the right list (the head reads the first cell of the right list).

The anchor is `T Y m c Z` = `Y 1^m D> 0 1^c Z`: state D on a single 0, a block of `m` ones on its left (then the
list `Y`), a block of `c` ones after it (then the list `Z`).  `evT` gives, for every case that is modelled, the next
anchor (the events `zero`, `one`, `oneE`, `oneO`, `two`, `shift`, `odd`, `fold`, `split`).  The map `F` applies an
event when the state is an anchor with a modelled case, and one machine step otherwise.

Main results:
* `event_sem`: an event is a run of the machine (at least one step);
* `F_sem`: `F s = some s'` → the machine goes from `s` to `s'`; `F s = none` → `s` is a halting configuration;
* `halts_iff`: **the machine halts from blank tape iff the orbit of the blank tape under `F` reaches `none`**;
* `events_forever`: if the event map alone can be iterated for ever from the first anchor, the machine never halts.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace H170561

open TM

/-! ## Reaching -/

/-- `c` reaches `c'` in at least one step. -/
def Reach (c c' : Config) : Prop := ∃ n, steps (n + 1) c = some c'
/-- `c` reaches `c'` (possibly in no step). -/
def Reaches (c c' : Config) : Prop := ∃ n, steps n c = some c'

theorem Reaches.trans {a b c : Config} : Reaches a b → Reaches b c → Reaches a c
  | ⟨n, h1⟩, ⟨m, h2⟩ => ⟨n + m, steps_seq H170561.trans h1 h2⟩
theorem reach_reaches {a b c : Config} : Reach a b → Reaches b c → Reach a c
  | ⟨n, h1⟩, ⟨m, h2⟩ => ⟨n + m, steps_congr trans (by omega) (steps_seq trans h1 h2)⟩
theorem reaches_reach {a b c : Config} : Reaches a b → Reach b c → Reach a c
  | ⟨n, h1⟩, ⟨m, h2⟩ => ⟨n + m, steps_congr trans (by omega) (steps_seq trans h1 h2)⟩
theorem Reach.reaches {a b : Config} : Reach a b → Reaches a b
  | ⟨n, h⟩ => ⟨n + 1, h⟩
theorem Reach.trans {a b c : Config} (h1 : Reach a b) (h2 : Reach b c) : Reach a c := reach_reaches h1 h2.reaches
theorem halts_pre {a b : Config} : Reaches a b → Halts trans b → Halts trans a
  | ⟨n, h1⟩, ⟨m, c, h2, h3⟩ => ⟨n + m, c, steps_seq trans h1 h2, h3⟩
/-- A run of a positive number of steps is a `Reach`. -/
theorem reach_of {n : Nat} {c c' : Config} (h : steps n c = some c') (hn : 0 < n) : Reach c c' :=
  ⟨n - 1, by rw [show n - 1 + 1 = n by omega]; exact h⟩
/-- A run between two configurations equal to the given ones. -/
theorem reach_of' {n : Nat} {c c' d d' : Config} (h : steps n d = some d') (e1 : c = d) (e2 : c' = d') (hn : 0 < n) :
    Reach c c' := by
  subst e1; subst e2; exact reach_of h hn

/-! ## Tape identities -/

theorem two_ones (n : Nat) (s : Tape) : rep n [true, true] s = rep (2 * n) [true] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show app [true, true] (rep n [true, true] s) = rep (2 * n + 1 + 1) [true] s
    rw [ih]; rfl
theorem ones_cons (n : Nat) (s : Tape) : rep n [true] (cons true s) = rep (n + 1) [true] s :=
  rep_app_comm n [true] s
theorem ones_ones (a b : Nat) (s : Tape) : rep a [true] (rep b [true] s) = rep (a + b) [true] s :=
  (rep_add a b [true] s).symm
theorem zeros_zeros (a b : Nat) (s : Tape) : rep a [false] (rep b [false] s) = rep (a + b) [false] s :=
  (rep_add a b [false] s).symm
theorem zeros_blank (n : Nat) : rep n [false] blank = blank := by
  induction n with
  | zero => rfl
  | succ n ih => show cons false (rep n [false] blank) = blank; rw [ih]; exact cons_false_blank
theorem rep_congr {a b : Nat} {w : List Bool} {s t : Tape} (h1 : a = b) (h2 : s = t) : rep a w s = rep b w t := by
  subst h1; subst h2; rfl

/-! ## Run-length tapes -/

/-- One side of the tape, nearest the head first: pairs (number of 0s, number of 1s); blank beyond. -/
abbrev Side := List (Nat × Nat)

/-- The cells of a side. -/
def dec : Side → Tape
  | [] => blank
  | (g, b) :: s => rep g [false] (rep b [true] (dec s))

/-- The nearest cell. -/
def hd : Side → Bool
  | [] => false
  | (_ + 1, _) :: _ => false
  | (0, _ + 1) :: _ => true
  | (0, 0) :: s => hd s
/-- Remove the nearest cell. -/
def pop : Side → Side
  | [] => []
  | (g + 1, b) :: s => (g, b) :: s
  | (0, b + 2) :: s => (0, b + 1) :: s
  | (0, 1) :: s => s
  | (0, 0) :: s => pop s
/-- Put `n` ones in front. -/
def push1s (n : Nat) : Side → Side
  | (0, b) :: s => (0, b + n) :: s
  | s => if n = 0 then s else (0, n) :: s
/-- Put `n` zeros in front. -/
def push0s (n : Nat) : Side → Side
  | [] => []
  | (g, b) :: s => (g + n, b) :: s
/-- Put one cell in front. -/
def push (x : Bool) (s : Side) : Side := if x then push1s 1 s else push0s 1 s

theorem dec_split : ∀ s : Side, dec s = cons (hd s) (dec (pop s))
  | [] => cons_false_blank.symm
  | (_ + 1, _) :: _ => rfl
  | (0, _ + 2) :: _ => rfl
  | (0, 1) :: _ => rfl
  | (0, 0) :: s => dec_split s
theorem dec_hd (s : Side) : dec s 0 = hd s := by rw [dec_split s]; rfl
theorem dec_pop (s : Side) : tail (dec s) = dec (pop s) := by rw [dec_split s]; rfl
theorem dec_push1s (n : Nat) : ∀ s : Side, dec (push1s n s) = rep n [true] (dec s)
  | [] => by
    by_cases h : n = 0
    · subst h; rfl
    · simp only [push1s, if_neg h]; rfl
  | (0, b) :: s => by
    show rep (b + n) [true] (dec s) = rep n [true] (rep b [true] (dec s))
    rw [ones_ones, Nat.add_comm]
  | (g + 1, b) :: s => by
    by_cases h : n = 0
    · subst h; rfl
    · simp only [push1s, if_neg h]; rfl
theorem dec_push0s (n : Nat) : ∀ s : Side, dec (push0s n s) = rep n [false] (dec s)
  | [] => (zeros_blank n).symm
  | (g, b) :: s => by
    show rep (g + n) [false] _ = rep n [false] (rep g [false] _)
    rw [zeros_zeros, Nat.add_comm]
theorem dec_push (x : Bool) (s : Side) : dec (push x s) = cons x (dec s) := by
  cases x
  · simp only [push]; exact dec_push0s 1 s
  · simp only [push]; exact dec_push1s 1 s
/-- A side whose nearest cell is 0. -/
theorem dec_zero {s : Side} (h : hd s = false) : dec s = cons false (dec (pop s)) := by
  have := dec_split s; rw [h] at this; exact this
/-- A side whose nearest cell is 1. -/
theorem dec_one {s : Side} (h : hd s = true) : dec s = cons true (dec (pop s)) := by
  have := dec_split s; rw [h] at this; exact this

/-- A configuration by run lengths. -/
structure RS where
  l : Side
  q : St
  r : Side
  deriving DecidableEq, Repr

/-- The configuration it stands for. -/
def cfg (s : RS) : Config := ⟨dec s.l, dec s.r, s.q⟩

/-- One machine step on run lengths. -/
def rstep (s : RS) : Option RS :=
  match trans s.q (hd s.r) with
  | none => none
  | some (w, .R, q') => some ⟨push w s.l, q', pop s.r⟩
  | some (w, .L, q') => some ⟨pop s.l, q', push (hd s.l) (push w (pop s.r))⟩

theorem rstep_sem (s : RS) : step (cfg s) = (rstep s).map cfg := by
  simp only [step, TM.step, rstep, cfg, dec_hd]
  cases h : trans s.q (hd s.r) with
  | none => rfl
  | some t =>
    obtain ⟨w, d, q'⟩ := t
    cases d
    · simp only [Option.map, cfg, dec_push, dec_pop, dec_hd]
    · simp only [Option.map, cfg, dec_push, dec_pop, dec_hd]

/-! ## The rounds, with blocks of ones as `rep n [true]` -/

theorem cfg_eq {l l' r r' : Tape} {q : St} (h1 : l = l') (h2 : r = r') : (⟨l, r, q⟩ : Config) = ⟨l', r', q⟩ := by
  subst h1; subst h2; rfl

/-- `L 0 1^(2j+3) D> 0 R` → `L 1^(2j+1) D> 0 1^3 R`. -/
theorem c_odd (j : Nat) (L R : Tape) :
    Reach ⟨rep (2 * j + 3) [true] (cons false L), cons false R, .D⟩ ⟨rep (2 * j + 1) [true] L, cons false (rep 3 [true] R), .D⟩ := by
  refine reach_of' (r_odd j L R) (cfg_eq ?_ rfl) (cfg_eq ?_ rfl) (by omega)
  · rw [two_ones, ones_cons]; exact rep_congr (by omega) rfl
  · rw [two_ones]; rfl

/-- `L 0 1^(2j+2) D> 0 R` → `L D> 0 1^(2j+1) 0 0 R`. -/
theorem c_shift (j : Nat) (L R : Tape) :
    Reach ⟨rep (2 * j + 2) [true] (cons false L), cons false R, .D⟩
      ⟨L, cons false (rep (2 * j + 1) [true] (cons false (cons false R))), .D⟩ := by
  refine reach_of' (r_shift j L R) (cfg_eq ?_ rfl) (cfg_eq rfl ?_) (by omega)
  · rw [two_ones]; exact rep_congr (by omega) rfl
  · rw [two_ones]; rfl

/-- `L 0 0 1^(2j+4) D> 0 R` → `L 1 0 0 1^(2j) D> 0 1^3 R`. -/
theorem c_split1 (j : Nat) (L R : Tape) :
    Reach ⟨rep (2 * j + 4) [true] (cons false (cons false L)), cons false R, .D⟩
      ⟨rep (2 * j) [true] (cons false (cons false (cons true L))), cons false (rep 3 [true] R), .D⟩ := by
  refine reach_of' (r_split j L R) (cfg_eq ?_ rfl) (cfg_eq ?_ rfl) (by omega)
  · rw [two_ones]; exact rep_congr (by omega) rfl
  · rw [two_ones]

/-- `L 0 1^(2j+1) 0 1 D> 0 R` → `L D> 0 1^(2j+3) 0 R`. -/
theorem c_oneO (j : Nat) (L R : Tape) :
    Reach ⟨cons true (cons false (rep (2 * j + 1) [true] (cons false L))), cons false R, .D⟩
      ⟨L, cons false (rep (2 * j + 3) [true] (cons false R)), .D⟩ := by
  refine reach_of' (r_oneO j L R) (cfg_eq ?_ rfl) (cfg_eq rfl ?_) (by omega)
  · rw [two_ones, ones_cons]
  · rw [two_ones]; rfl

/-- `L 0 1^(2j+2) 0 1 D> 0 1^(k+2) R` → `L 1^(2j+3) 0 1^(k+2) 0 1 A> R`. -/
theorem c_oneE (j k : Nat) (L R : Tape) :
    Reach ⟨cons true (cons false (rep (2 * j + 2) [true] (cons false L))), cons false (rep (k + 2) [true] R), .D⟩
      ⟨cons true (cons false (rep (k + 2) [true] (cons false (rep (2 * j + 3) [true] L)))), R, .A⟩ := by
  refine reach_of' (r_oneE j k L R) (cfg_eq ?_ rfl) (cfg_eq ?_ rfl) (by omega)
  · rw [two_ones]; rfl
  · rw [two_ones, ones_cons, ones_cons]; rfl

/-- `L 0 D> 0 1^(k+3) R` → `L 1 0 0 1^k 0 1 A> R`. -/
theorem c_zero (k : Nat) (L R : Tape) :
    Reach ⟨cons false L, cons false (rep (k + 3) [true] R), .D⟩
      ⟨cons true (cons false (rep k [true] (cons false (cons false (cons true L))))), R, .A⟩ :=
  reach_of (r_zero k L R) (by omega)

/-- `L 0 0 1 1 D> 0 1^(k+2) R` → `L 1 0 0 0 0 1^k 0 1 A> R`. -/
theorem c_two (k : Nat) (L R : Tape) :
    Reach ⟨rep 2 [true] (cons false (cons false L)), cons false (rep (k + 2) [true] R), .D⟩
      ⟨cons true (cons false (rep k [true] (rep 4 [false] (cons true L)))), R, .A⟩ :=
  reach_of (r_two k L R) (by omega)

/-- `L 0 0 1 D> 0 1^(k+2) R` → `L 1 0 1^(k+2) 0 1 A> R`. -/
theorem c_one (k : Nat) (L R : Tape) :
    Reach ⟨rep 1 [true] (cons false (cons false L)), cons false (rep (k + 2) [true] R), .D⟩
      ⟨cons true (cons false (rep (k + 2) [true] (cons false (cons true L)))), R, .A⟩ := by
  refine reach_of' (r_one k L R) rfl (cfg_eq ?_ rfl) (by omega)
  rw [ones_cons, ones_cons]

/-- The carrier passes a block after one 0: `L 0 1 A> 0 1^(b+2) R` → `L 0 1^(b+2) 0 1 A> R`. -/
theorem c_pass (b : Nat) (L R : Tape) :
    Reach ⟨cons true (cons false L), cons false (rep (b + 2) [true] R), .A⟩
      ⟨cons true (cons false (rep (b + 2) [true] (cons false L))), R, .A⟩ := by
  refine reach_of' (a_pass b L R) rfl (cfg_eq ?_ rfl) (by omega)
  rw [ones_cons, ones_cons]

/-! ## The accelerated rounds -/

/-- The fold: at the left end of the tape, `1^(2k+1) D> 0 R` → `1 D> 0 1^(3k) R`. -/
theorem c_fold (k : Nat) : ∀ R : Tape,
    Reaches ⟨rep (2 * k + 1) [true] blank, cons false R, .D⟩ ⟨rep 1 [true] blank, cons false (rep (3 * k) [true] R), .D⟩ := by
  induction k with
  | zero => intro R; exact ⟨0, rfl⟩
  | succ k ih =>
    intro R
    have h1 := c_odd k blank R
    rw [cons_false_blank] at h1
    have h2 := ih (rep 3 [true] R)
    rw [ones_ones] at h2
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 by omega, show 3 * (k + 1) = 3 * k + 3 by omega]
    exact h1.reaches.trans h2

/-- The split: `L 0 0 1^(4q+2i) D> 0 R` → `L 1^q 0 0 1^(2i) D> 0 1^(3q) R`. -/
theorem c_split (i q : Nat) : ∀ L R : Tape,
    Reaches ⟨rep (4 * q + 2 * i) [true] (cons false (cons false L)), cons false R, .D⟩
      ⟨rep (2 * i) [true] (cons false (cons false (rep q [true] L))), cons false (rep (3 * q) [true] R), .D⟩ := by
  induction q with
  | zero => intro L R; exact ⟨0, by rw [show 4 * 0 + 2 * i = 2 * i by omega]; rfl⟩
  | succ q ih =>
    intro L R
    have h1 := c_split1 (2 * q + i) L R
    have h2 := ih (cons true L) (rep 3 [true] R)
    rw [ones_ones, ones_cons] at h2
    rw [show 2 * (2 * q + i) + 4 = 4 * (q + 1) + 2 * i by omega, show 2 * (2 * q + i) = 4 * q + 2 * i by omega] at h1
    rw [show 3 * (q + 1) = 3 * q + 3 by omega]
    exact h1.reaches.trans h2

/-! ## The carrier's arrival -/

/-- `arr l Z`: the carrier `0 1`, with the side `l` behind it, arrives at the side `Z` (`l 0 1 A> Z`).  It passes
every block of at least two 1s that follows a single 0, and stops at two 0s (or at the end of the tape), where it
becomes three 1s.  `none`: not modelled (a single 1 after a single 0, or no 0 at all). -/
def arr : Side → Side → Option RS
  | l, [] => some ⟨l, .D, [(1, 3)]⟩
  | l, (1, b + 2) :: Z => arr (push1s (b + 2) (push0s 1 l)) Z
  | l, (2, b) :: Z => some ⟨l, .D, (1, b + 3) :: Z⟩
  | l, (g + 3, b) :: Z => some ⟨l, .D, (1, 3) :: (g + 1, b) :: Z⟩
  | _, _ => none

theorem arr_sem : ∀ (Z l : Side) (s : RS), arr l Z = some s →
    Reach ⟨cons true (cons false (dec l)), dec Z, .A⟩ (cfg s)
  | [], l, s, h => by
    simp only [arr, Option.some.injEq] at h; subst h
    have h1 := a_end (dec l) blank
    rw [cons_false_blank, cons_false_blank] at h1
    exact reach_of h1 (by omega)
  | (0, _) :: _, _, _, h => by simp [arr] at h
  | (1, 0) :: _, _, _, h => by simp [arr] at h
  | (1, 1) :: _, _, _, h => by simp [arr] at h
  | (1, b + 2) :: Z, l, s, h => by
    simp only [arr] at h
    have h2 := arr_sem Z _ s h
    rw [dec_push1s, dec_push0s] at h2
    exact (c_pass b (dec l) (dec Z)).trans h2
  | (2, b) :: Z, l, s, h => by
    simp only [arr, Option.some.injEq] at h; subst h
    exact reach_of (a_end (dec l) (rep b [true] (dec Z))) (by omega)
  | (g + 3, b) :: Z, l, s, h => by
    simp only [arr, Option.some.injEq] at h; subst h
    exact reach_of (a_end (dec l) (rep (g + 1) [false] (rep b [true] (dec Z)))) (by omega)

/-! ## The events -/

/-- The anchor `Y 1^m D> 0 1^c Z`. -/
def Tcfg (Y : Side) (m c : Nat) (Z : Side) : Config :=
  ⟨rep m [true] (dec Y), cons false (rep c [true] (dec Z)), .D⟩

/-- The event at the anchor `Y 1^m D> 0 1^c Z` (`none`: not modelled). -/
def evT (Y : Side) (m c : Nat) (Z : Side) : Option RS :=
  if hd Y then none
  else if m = 0 then
    -- zero: `Y' 0 D> 0 1^c Z` → `Y' 1 0 0 1^(c-3) 0 1 A> Z`
    if 3 ≤ c then arr (push1s (c - 3) (push0s 2 (push1s 1 (pop Y)))) Z else none
  else if m = 1 then
    if hd (pop Y) then
      match pop Y with
      | (0, a) :: Y' =>
        if hd Y' then none
        else if a % 2 = 0 then
          -- oneE: `Y'' 0 1^a 0 1 D> 0 1^c Z` → `Y'' 1^(a+1) 0 1^c 0 1 A> Z`, a even
          (if 2 ≤ a ∧ 2 ≤ c then arr (push1s c (push0s 1 (push1s (a + 1) (pop Y')))) Z else none)
        else
          -- oneO: `Y'' 0 1^a 0 1 D> 0 1^c Z` → `Y'' D> 0 1^(a+2) 0 1^c Z`, a odd
          some ⟨pop Y', .D, (1, a + 2) :: (1, c) :: Z⟩
      | _ => none
    else
      -- one: `Y' 0 0 1 D> 0 1^c Z` → `Y' 1 0 1^c 0 1 A> Z`
      if 2 ≤ c then arr (push1s c (push0s 1 (push1s 1 (pop (pop Y))))) Z else none
  else if m % 2 = 1 then
    match Y with
    -- fold: `1^m D> 0 1^c Z` → `1 D> 0 1^(c + 3(m-1)/2) Z` at the left end of the tape
    | [] => some ⟨[(0, 1)], .D, (1, c + 3 * (m / 2)) :: Z⟩
    -- odd: `Y' 0 1^m D> 0 1^c Z` → `Y' 1^(m-2) D> 0 1^(c+3) Z`
    | _ => some ⟨push1s (m - 2) (pop Y), .D, (1, c + 3) :: Z⟩
  else if hd (pop Y) then
    -- shift: `Y' 1 0 1^m D> 0 1^c Z` → `Y' 1 D> 0 1^(m-1) 0 0 1^c Z`
    some ⟨pop Y, .D, (1, m - 1) :: (2, c) :: Z⟩
  else if m = 2 then
    -- two: `Y' 0 0 1 1 D> 0 1^c Z` → `Y' 1 0 0 0 0 1^(c-2) 0 1 A> Z`
    if 2 ≤ c then arr (push1s (c - 2) (push0s 4 (push1s 1 (pop (pop Y))))) Z else none
  else
    -- split: `Y' 0 0 1^m D> 0 1^c Z` → `Y' 1^(m/4) 0 0 1^(m%4) D> 0 1^(c + 3(m/4)) Z`
    some ⟨push1s (m % 4) (push0s 2 (push1s (m / 4) (pop (pop Y)))), .D, (1, c + 3 * (m / 4)) :: Z⟩

theorem evT_sem (Y : Side) (m c : Nat) (Z : Side) (s : RS) (h : evT Y m c Z = some s) :
    Reach (Tcfg Y m c Z) (cfg s) := by
  unfold evT at h
  by_cases hY : hd Y = true
  · simp [hY] at h
  have hY0 : hd Y = false := by simpa using hY
  simp only [hY0, Bool.false_eq_true, if_false] at h
  have eY : dec Y = cons false (dec (pop Y)) := dec_zero hY0
  unfold Tcfg; rw [eY]
  by_cases hm0 : m = 0
  · -- zero
    subst hm0
    simp only [if_true] at h
    by_cases hc : 3 ≤ c
    · rw [if_pos hc] at h
      obtain ⟨k, rfl⟩ : ∃ k, c = k + 3 := ⟨c - 3, by omega⟩
      have h2 := arr_sem Z _ s h
      rw [dec_push1s, dec_push0s, dec_push1s, show k + 3 - 3 = k by omega] at h2
      exact (c_zero k (dec (pop Y)) (dec Z)).trans h2
    · rw [if_neg hc] at h; cases h
  rw [if_neg hm0] at h
  by_cases hm1 : m = 1
  · subst hm1
    simp only [if_true] at h
    by_cases hP : hd (pop Y) = true
    · rw [if_pos hP] at h
      have eP : dec (pop Y) = cons true (dec (pop (pop Y))) := dec_one hP
      match hpy : pop Y, h with
      | (0, a) :: Y', h =>
        simp only at h
        by_cases hY' : hd Y' = true
        · simp [hY'] at h
        have hY'0 : hd Y' = false := by simpa using hY'
        simp only [hY'0, Bool.false_eq_true, if_false] at h
        have eY' : dec Y' = cons false (dec (pop Y')) := dec_zero hY'0
        have e1 : dec ((0, a) :: Y') = rep a [true] (cons false (dec (pop Y'))) := by rw [← eY']; rfl
        rw [e1]
        by_cases ha : a % 2 = 0
        · rw [if_pos ha] at h
          by_cases hc : 2 ≤ a ∧ 2 ≤ c
          · rw [if_pos hc] at h
            obtain ⟨j, rfl⟩ : ∃ j, a = 2 * j + 2 := ⟨a / 2 - 1, by omega⟩
            obtain ⟨k, rfl⟩ : ∃ k, c = k + 2 := ⟨c - 2, by omega⟩
            have h2 := arr_sem Z _ s h
            rw [dec_push1s, dec_push0s, dec_push1s] at h2
            exact (c_oneE j k (dec (pop Y')) (dec Z)).trans h2
          · rw [if_neg hc] at h; cases h
        · rw [if_neg ha] at h
          simp only [Option.some.injEq] at h; subst h
          obtain ⟨j, rfl⟩ : ∃ j, a = 2 * j + 1 := ⟨a / 2, by omega⟩
          exact c_oneO j (dec (pop Y')) (rep c [true] (dec Z))
      | [], h => simp at h
      | (_ + 1, _) :: _, h => simp at h
    · rw [if_neg hP] at h
      have hP0 : hd (pop Y) = false := by simpa using hP
      have eP : dec (pop Y) = cons false (dec (pop (pop Y))) := dec_zero hP0
      rw [eP]
      by_cases hc : 2 ≤ c
      · rw [if_pos hc] at h
        obtain ⟨k, rfl⟩ : ∃ k, c = k + 2 := ⟨c - 2, by omega⟩
        have h2 := arr_sem Z _ s h
        rw [dec_push1s, dec_push0s, dec_push1s] at h2
        exact (c_one k (dec (pop (pop Y))) (dec Z)).trans h2
      · rw [if_neg hc] at h; cases h
  rw [if_neg hm1] at h
  by_cases hodd : m % 2 = 1
  · rw [if_pos hodd] at h
    obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 3 := ⟨(m - 3) / 2, by omega⟩
    match hy : Y, h with
    | [], h =>
      simp only [Option.some.injEq] at h; subst h
      rw [← eY]
      have h0 := c_odd j blank (rep c [true] (dec Z))
      rw [cons_false_blank, ones_ones] at h0
      have h3 := c_fold j (rep 3 [true] (rep c [true] (dec Z)))
      rw [ones_ones, ones_ones] at h3
      refine reach_of' (reach_reaches h0 h3).choose_spec ?_ ?_ (by omega)
      · rfl
      · show (⟨rep 1 [true] blank, cons false (rep (c + 3 * ((2 * j + 3) / 2)) [true] (dec Z)), .D⟩ : Config) = _
        exact cfg_eq rfl (congrArg _ (rep_congr (by omega) rfl))
    | p :: Y', h =>
      simp only [Option.some.injEq] at h; subst h
      have h0 := c_odd j (dec (pop (p :: Y'))) (rep c [true] (dec Z))
      rw [ones_ones] at h0
      refine reach_of' h0.choose_spec rfl ?_ (by omega)
      show (⟨dec (push1s (2 * j + 3 - 2) (pop (p :: Y'))), cons false (rep (c + 3) [true] (dec Z)), .D⟩ : Config) = _
      rw [dec_push1s]
      exact cfg_eq (rep_congr (by omega) rfl) (congrArg _ (rep_congr (by omega) rfl))
  rw [if_neg hodd] at h
  by_cases hP : hd (pop Y) = true
  · -- shift
    rw [if_pos hP] at h
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 2 := ⟨(m - 2) / 2, by omega⟩
    have h0 := c_shift j (dec (pop Y)) (rep c [true] (dec Z))
    refine reach_of' h0.choose_spec rfl ?_ (by omega)
    show (⟨dec (pop Y), cons false (rep (2 * j + 2 - 1) [true] (cons false (cons false (rep c [true] (dec Z))))), .D⟩ : Config) = _
    exact cfg_eq rfl (congrArg _ (rep_congr (by omega) rfl))
  rw [if_neg hP] at h
  have hP0 : hd (pop Y) = false := by simpa using hP
  have eP : dec (pop Y) = cons false (dec (pop (pop Y))) := dec_zero hP0
  rw [eP]
  by_cases hm2 : m = 2
  · subst hm2
    simp only [if_true] at h
    by_cases hc : 2 ≤ c
    · rw [if_pos hc] at h
      obtain ⟨k, rfl⟩ : ∃ k, c = k + 2 := ⟨c - 2, by omega⟩
      have h2 := arr_sem Z _ s h
      rw [dec_push1s, dec_push0s, dec_push1s, show k + 2 - 2 = k by omega] at h2
      exact (c_two k (dec (pop (pop Y))) (dec Z)).trans h2
    · rw [if_neg hc] at h; cases h
  · -- split
    rw [if_neg hm2] at h
    simp only [Option.some.injEq] at h; subst h
    have hq : 1 ≤ m / 4 := by omega
    obtain ⟨i, hi⟩ : ∃ i, m % 4 = 2 * i := ⟨m % 4 / 2, by omega⟩
    have h1 := c_split i (m / 4 - 1) (cons true (dec (pop (pop Y)))) (rep 3 [true] (rep c [true] (dec Z)))
    have h0 := c_split1 (2 * (m / 4 - 1) + i) (dec (pop (pop Y))) (rep c [true] (dec Z))
    rw [show 2 * (2 * (m / 4 - 1) + i) + 4 = m by omega, show 2 * (2 * (m / 4 - 1) + i) = 4 * (m / 4 - 1) + 2 * i by omega, ones_ones] at h0
    rw [ones_ones, ones_ones, ones_cons] at h1
    refine reach_of' (reach_reaches h0 h1).choose_spec rfl ?_ (by omega)
    show (⟨dec (push1s (m % 4) (push0s 2 (push1s (m / 4) (pop (pop Y))))), cons false (rep (c + 3 * (m / 4)) [true] (dec Z)), .D⟩ : Config) = _
    rw [dec_push1s, dec_push0s, dec_push1s]
    have e2 : rep (m / 4) [true] (dec (pop (pop Y))) = rep (m / 4 - 1 + 1) [true] (dec (pop (pop Y))) :=
      rep_congr (by omega) rfl
    have e3 : rep 2 [false] (rep (m / 4) [true] (dec (pop (pop Y))))
        = cons false (cons false (rep (m / 4 - 1 + 1) [true] (dec (pop (pop Y))))) := by rw [← e2]; rfl
    exact cfg_eq (rep_congr (by omega) e3) (congrArg _ (rep_congr (by omega) rfl))

/-- The event at a state: the state must be an anchor `Y 1^m D> 0 1^c Z` (`none`: it is not, or its case is not
modelled). -/
def event (s : RS) : Option RS :=
  match s with
  | ⟨(0, m) :: Y, .D, (1, c) :: Z⟩ => evT Y m c Z
  | ⟨Y, .D, (1, c) :: Z⟩ => evT Y 0 c Z
  | _ => none

/-- **An event is a run of the machine**, of at least one step. -/
theorem event_sem (s s' : RS) (h : event s = some s') : Reach (cfg s) (cfg s') := by
  unfold event at h
  split at h
  · exact evT_sem _ _ _ _ _ h
  · exact evT_sem _ _ _ _ _ h
  · cases h

/-! ## The map -/

/-- The map: an event where one applies, one machine step otherwise. -/
def F (s : RS) : Option RS :=
  match event s with
  | some s' => some s'
  | none => rstep s

/-- `F s = some s'`: the machine goes from `s` to `s'`.  `F s = none`: `s` is a halting configuration. -/
theorem F_sem (s : RS) :
    match F s with
    | some s' => Reach (cfg s) (cfg s')
    | none => step (cfg s) = none := by
  unfold F
  cases he : event s with
  | some s' => exact event_sem s s' he
  | none =>
    show match rstep s with
      | some s' => Reach (cfg s) (cfg s')
      | none => step (cfg s) = none
    have hr := rstep_sem s
    cases hs : rstep s with
    | none => rw [hs] at hr; exact hr
    | some s' =>
      rw [hs] at hr
      have hr' : step (cfg s) = some (cfg s') := hr
      exact ⟨0, (steps_succ_of_step trans 0 hr').trans rfl⟩

/-- The orbit of `s` under `F`. -/
def orbitFrom (s : RS) : Nat → Option RS
  | 0 => some s
  | k + 1 => (F s).bind (fun s' => orbitFrom s' k)

theorem runs_long (N : Nat) : ∀ s : RS, (∀ k, orbitFrom s k ≠ none) →
    ∃ m, N ≤ m ∧ ∃ c, steps m (cfg s) = some c := by
  induction N with
  | zero => intro s _; exact ⟨0, Nat.le_refl 0, _, rfl⟩
  | succ N ih =>
    intro s hs
    cases hF : F s with
    | none => exact absurd (by simp [orbitFrom, hF]) (hs 1)
    | some s' =>
      have hs' : ∀ k, orbitFrom s' k ≠ none := fun k h => hs (k + 1) (by simp [orbitFrom, hF, h])
      obtain ⟨m, hm, c, hc⟩ := ih s' hs'
      have hr := F_sem s
      rw [hF] at hr
      obtain ⟨k, hk⟩ := hr
      exact ⟨k + 1 + m, by omega, c, steps_seq trans hk hc⟩

/-- The machine halts from the state `s` iff the orbit of `s` under `F` reaches `none`. -/
theorem halts_from (s : RS) : Halts trans (cfg s) ↔ ∃ k, orbitFrom s k = none := by
  constructor
  · intro hh
    refine Classical.byContradiction fun hne => ?_
    have hs : ∀ k, orbitFrom s k ≠ none := fun k h => hne ⟨k, h⟩
    refine not_halts_of_forall trans ?_ hh
    exact forall_of_unbounded trans (fun m => ∃ c, steps m (cfg s) = some c) (runs_long · s hs) (fun _ h => h)
  · rintro ⟨k, hk⟩
    induction k generalizing s with
    | zero => simp [orbitFrom] at hk
    | succ k ih =>
      have hr := F_sem s
      cases hF : F s with
      | none => rw [hF] at hr; exact ⟨0, cfg s, rfl, hr⟩
      | some s' =>
        rw [hF] at hr
        have hk' : orbitFrom s' k = none := by simpa [orbitFrom, hF] using hk
        exact halts_pre hr.reaches (ih s' hk')

/-- The blank tape, state A. -/
def start : RS := ⟨[], .A, []⟩

/-- **Main theorem.** The machine halts from blank tape iff the orbit of the blank tape under the map `F` (an event
at every anchor whose case is modelled, one machine step otherwise) reaches `none`, that is, a configuration in
state F reading 0. -/
theorem halts_iff : HaltsFromBlank ↔ ∃ k, orbitFrom start k = none :=
  halts_from start

/-! ## Events only -/

/-- The orbit of `s` under the events alone. -/
def evOrbit (s : RS) : Nat → Option RS
  | 0 => some s
  | k + 1 =>
    match event s with
    | none => none
    | some s' => evOrbit s' k

theorem evOrbit_reaches : ∀ (k : Nat) (s s' : RS), evOrbit s k = some s' → Reaches (cfg s) (cfg s')
  | 0, s, s', h => by simp only [evOrbit, Option.some.injEq] at h; subst h; exact ⟨0, rfl⟩
  | k + 1, s, s', h => by
    simp only [evOrbit] at h
    cases he : event s with
    | none => rw [he] at h; cases h
    | some s1 =>
      rw [he] at h
      exact (event_sem s s1 he).reaches.trans (evOrbit_reaches k s1 s' h)

theorem ev_runs_long (N : Nat) : ∀ s : RS, (∀ k, evOrbit s k ≠ none) →
    ∃ m, N ≤ m ∧ ∃ c, steps m (cfg s) = some c := by
  induction N with
  | zero => intro s _; exact ⟨0, Nat.le_refl 0, _, rfl⟩
  | succ N ih =>
    intro s hs
    cases hF : event s with
    | none => exact absurd (by simp [evOrbit, hF]) (hs 1)
    | some s' =>
      have hs' : ∀ k, evOrbit s' k ≠ none := fun k h => hs (k + 1) (by simpa [evOrbit, hF] using h)
      obtain ⟨m, hm, c, hc⟩ := ih s' hs'
      obtain ⟨k, hk⟩ := event_sem s s' hF
      exact ⟨k + 1 + m, by omega, c, steps_seq trans hk hc⟩

/-- The first anchor of the run from blank tape: `1 D> 0 1 1 1`, after 14 steps. -/
def first : RS := ⟨[(0, 1)], .D, [(1, 3)]⟩

theorem start_first : orbitFrom start 14 = some first := by decide

theorem orbit_reaches : ∀ (k : Nat) (s s' : RS), orbitFrom s k = some s' → Reaches (cfg s) (cfg s')
  | 0, s, s', h => by simp only [orbitFrom, Option.some.injEq] at h; subst h; exact ⟨0, rfl⟩
  | k + 1, s, s', h => by
    simp only [orbitFrom] at h
    have hr := F_sem s
    cases he : F s with
    | none => rw [he] at h; cases h
    | some s1 =>
      rw [he] at h hr
      exact hr.reaches.trans (orbit_reaches k s1 s' h)

theorem blank_first : Reaches init (cfg first) := orbit_reaches 14 start first start_first

/-- **If the events alone can be iterated for ever from the first anchor, the machine never halts.**  So a halt
needs an anchor whose case is not modelled. -/
theorem events_forever (h : ∀ k, evOrbit first k ≠ none) : ¬ HaltsFromBlank := by
  obtain ⟨n0, h0⟩ := blank_first
  refine not_halts_of_forall trans ?_
  refine forall_of_unbounded trans (fun m => ∃ c, steps m init = some c) (fun N => ?_) (fun _ h => h)
  obtain ⟨m, hm, c, hc⟩ := ev_runs_long N first h
  exact ⟨n0 + m, by omega, c, steps_seq trans h0 hc⟩

end H170561
