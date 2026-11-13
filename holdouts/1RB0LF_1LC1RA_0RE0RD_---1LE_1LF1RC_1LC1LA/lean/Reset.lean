import Leaves

/-!
# The reset map of 1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA, proved

Configurations (tapes read left to right, the head reads the cell after `S>`):

* `Zc t`   = `1^t A>`                       (a solid block, A on the blank cell to its right; `Zc 0` is blank tape)
* `Wc x y` = `(10)^x 1^y A>`                (the bouncer between resets)
* `Rc a c` = `C> 0 1 (01)^a 1^c`            (a round of the odd reset, head at the left end)
* `Ic m i c` = `1 (01)^m A> 0 1 (01)^(2i) 1^c` (inside a round: pairs 01 move from the left block to the right one)

The leaf rules are in `Leaves.lean` (written by `bbtools.symtm.prove`); this file restates them on these
configurations, does the inductions (the sweeps of the bouncer, the steps of a round, the rounds of a reset) and
assembles them into a map `F` on the states `z t` (= `Zc t`) and `rs d` (= `Rc 0 (2d+3)`, a restart of the rounds).

Main results:
* `F_sem`: `F s = some s'` → the machine goes from `s` to `s'` (at least one step); `F s = none` → it halts from `s`;
* `halts_iff`: **the machine halts from blank tape iff the orbit of `z 0` under `F` reaches `none`**;
* `halts_iff_44`: the same for the orbit of `z 44` (blank tape reaches `Zc 19`, then `Zc 44`).
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace H165234

open TM

/-! ## Tape identities -/

theorem n_pair (n : Nat) (s : Tape) : rep n [true, true] s = rep (2 * n) [true] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show app [true, true] (rep n [true, true] s) = rep (2 * n + 1 + 1) [true] s
    rw [ih]; rfl
theorem n_quad (n : Nat) (s : Tape) : rep n [true, true, true, true] s = rep (4 * n) [true] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show app [true, true, true, true] (rep n [true, true, true, true] s) = rep (4 * n + 1 + 1 + 1 + 1) [true] s
    rw [ih]; rfl
theorem n_quad01 (n : Nat) (s : Tape) : rep n [false, true, false, true] s = rep (2 * n) [false, true] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show app [false, true, false, true] (rep n [false, true, false, true] s) = rep (2 * n + 1 + 1) [false, true] s
    rw [ih]; rfl
theorem n_cons1 (n : Nat) (s : Tape) : cons true (rep n [true] s) = rep (n + 1) [true] s := rfl
theorem n_1cons (n : Nat) (s : Tape) : rep n [true] (cons true s) = rep (n + 1) [true] s :=
  rep_app_comm n [true] s
theorem n_10 (n : Nat) (s : Tape) : rep n [true, false] (cons true s) = cons true (rep n [false, true] s) :=
  (rep_rotate n [true] [false, true] [true, false] rfl s).symm
theorem n_01 (n : Nat) (s : Tape) : rep n [false, true] (cons false (cons true s)) = rep (n + 1) [false, true] s :=
  rep_app_comm n [false, true] s
theorem n_01c (n c : Nat) (s : Tape) :
    rep n [false, true] (cons false (rep (c + 1) [true] s)) = rep (n + 1) [false, true] (rep c [true] s) :=
  rep_app_comm n [false, true] (rep c [true] s)
theorem n_01l (n : Nat) (s : Tape) : cons false (cons true (rep n [false, true] s)) = rep (n + 1) [false, true] s :=
  rfl
theorem n_1010 (n : Nat) (s : Tape) :
    cons false (rep n [true, false, true, false] s) = rep n [false, true, false, true] (cons false s) :=
  rep_rotate n [false] [true, false, true, false] [false, true, false, true] rfl s
theorem n_one01 (s : Tape) : rep 1 [false, true] s = cons false (cons true s) := rfl

/-- `0 1 (0101)^i 0 1^(c+1) = (0101)^(i+1) 1^c`: the right block after one step of a round. -/
theorem n_it (i c : Nat) (s : Tape) :
    cons false (cons true (rep i [false, true, false, true] (cons false (rep (c + 1) [true] s))))
      = rep (i + 1) [false, true, false, true] (rep c [true] s) := by
  show app [false, true] (rep i [false, true, false, true] (app [false, true] (rep c [true] s))) = _
  rw [rep_rotate i [false, true] [false, true, false, true] [false, true, false, true] rfl, app_app]
  exact rep_app_comm i [false, true, false, true] (rep c [true] s)

/-! ## The configurations -/

/-- `1^t A>`: a solid block of `t` ones, A on the blank cell after it. `Zc 0` is blank tape. -/
def Zc (t : Nat) : Config := ⟨rep t [true] blank, blank, .A⟩
/-- `(10)^x 1^y A>`. -/
def Wc (x y : Nat) : Config := ⟨rep y [true] (rep x [false, true] blank), blank, .A⟩
/-- `C> 0 1 (01)^a 1^c` at the left end. -/
def Rc (a c : Nat) : Config := ⟨blank, cons false (cons true (rep a [false, true] (rep c [true] blank))), .C⟩
/-- `1 (01)^m A> 0 1 (0101)^i 1^c`. -/
def Ic (m i c : Nat) : Config :=
  ⟨cons true (rep m [false, true] blank), cons false (cons true (rep i [false, true, false, true] (rep c [true] blank))), .A⟩

theorem Zc_eq_init : Zc 0 = init := rfl

/-! ## The leaf rules on these configurations -/

macro "norm_tape" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [n_pair, n_quad, n_quad01, n_cons1, n_1cons,
  n_10, n_01, n_01c, n_01l, n_1010, n_one01, cons_false_blank, rep_zero, Nat.mul_add, Nat.add_assoc, Nat.reduceAdd,
  Nat.reduceMul, Zc, Wc, Rc, Ic] $[$loc]?)

theorem w_sweep (x y : Nat) : steps (8 * y + 18) (Wc (x + 2) (2 * y + 1)) = some (Wc x (2 * y + 7)) := by
  have h := l_sweep x y; norm_tape at h; norm_tape; exact h
theorem w_sweep1 (y : Nat) : steps (8 * y + 18) (Wc 1 (2 * y + 1)) = some (Zc (2 * y + 6)) := by
  have h := l_sweep1 y; norm_tape at h; norm_tape; exact h
theorem z_even (k : Nat) : steps (4 * k + 36) (Zc (2 * k + 6)) = some (Wc (k + 1) 7) := by
  have h := l_even k; norm_tape at h; norm_tape; exact h
theorem z_odd (k : Nat) : steps (12 * k + 69) (Zc (2 * k + 7)) = some (Rc 0 (2 * k + 13)) := by
  have h := l_odd k; norm_tape at h; norm_tape; exact h
theorem r_zero (c : Nat) : steps 12 (Rc 0 (c + 2)) = some (Rc 2 c) := by
  have h := l_r0 c; norm_tape at h; norm_tape; exact h
theorem r_int (a c : Nat) : steps (2 * a + 8) (Rc (a + 1) (c + 2)) = some (Ic a 0 (c + 2)) := by
  have h := l_rint a c; norm_tape at h; norm_tape; exact h
theorem i_step (m i c : Nat) : steps (8 * i + 6) (Ic (m + 1) i (c + 2)) = some (Ic m (i + 1) c) := by
  have h := l_it c i m
  rw [n_10, n_10, n_it] at h
  exact h
theorem i_end1 (m i : Nat) : steps (12 * i + 10) (Ic (m + 1) i 1) = some (Wc m (4 * i + 5)) := by
  have h := l_iend1 i m; norm_tape at h; norm_tape; exact h
theorem i_fin (i c : Nat) : steps (16 * i + 20) (Ic 0 i (c + 4)) = some (Rc (2 * i + 4) c) := by
  have h := l_i0a c i; norm_tape at h; norm_tape; exact h
theorem i_fin3 (i : Nat) : steps (16 * i + 20) (Ic 0 i 3) = some (Rc (2 * i + 3) 0) := by
  have h := l_i0b i; norm_tape at h; norm_tape; exact h
theorem i_fin1 (i : Nat) : steps (12 * i + 10) (Ic 0 i 1) = some (Zc (4 * i + 4)) := by
  have h := l_i0c i; norm_tape at h; norm_tape; exact h
theorem r_restart (a : Nat) : steps (6 * a + 15) (Rc (a + 1) 0) = some (Rc 0 (2 * a + 5)) := by
  have h := l_rrs a; norm_tape at h; norm_tape; exact h
theorem r_halt (a : Nat) : Halts trans (Rc (a + 1) 1) :=
  ⟨2 * a + 5, _, l_rh a, rfl⟩

/-! ## Reaching -/

/-- `c` reaches `c'` in at least one step. -/
def Reach (c c' : Config) : Prop := ∃ n, steps (n + 1) c = some c'
/-- `c` reaches `c'` (possibly in no step). -/
def Reaches (c c' : Config) : Prop := ∃ n, steps n c = some c'

theorem Reaches.of {n : Nat} {c c' : Config} (h : steps n c = some c') : Reaches c c' := ⟨n, h⟩
theorem Reach.of {n : Nat} {c c' : Config} (h : steps (n + 1) c = some c') : Reach c c' := ⟨n, h⟩
theorem Reaches.trans {a b c : Config} : Reaches a b → Reaches b c → Reaches a c
  | ⟨n, h1⟩, ⟨m, h2⟩ => ⟨n + m, steps_seq H165234.trans h1 h2⟩
theorem reach_reaches {a b c : Config} : Reach a b → Reaches b c → Reach a c
  | ⟨n, h1⟩, ⟨m, h2⟩ => ⟨n + m, steps_congr trans (by omega) (steps_seq trans h1 h2)⟩
theorem reaches_reach {a b c : Config} : Reaches a b → Reach b c → Reach a c
  | ⟨n, h1⟩, ⟨m, h2⟩ => ⟨n + m, steps_congr trans (by omega) (steps_seq trans h1 h2)⟩
theorem Reach.reaches {a b : Config} : Reach a b → Reaches a b
  | ⟨n, h⟩ => ⟨n + 1, h⟩
theorem halts_pre {a b : Config} : Reaches a b → Halts trans b → Halts trans a
  | ⟨n, h1⟩, ⟨m, c, h2, h3⟩ => ⟨n + m, c, steps_seq trans h1 h2, h3⟩

/-! ## Inductions -/

/-- `j` steps of a round. -/
theorem i_iter (j : Nat) : ∀ m i c : Nat, Reaches (Ic (m + j) i (c + 2 * j)) (Ic m (i + j) c) := by
  induction j with
  | zero => intro m i c; exact ⟨0, rfl⟩
  | succ j ih =>
    intro m i c
    have h1 := i_step (m + j) i (c + 2 * j)
    have h2 := ih m (i + 1) c
    rw [show m + j + 1 = m + (j + 1) by omega, show c + 2 * j + 2 = c + 2 * (j + 1) by omega] at h1
    rw [show i + 1 + j = i + (j + 1) by omega] at h2
    exact (Reaches.of h1).trans h2

/-- Where the sweeps take `(10)^x 1^(2y+1) A>`: the block `1^(sweepv x y)`. -/
def sweepv (x y : Nat) : Nat := if x % 2 = 0 then 2 * y + 1 + 3 * x else 2 * y + 3 * x + 3

theorem w_even (b : Nat) : ∀ y : Nat, Reaches (Wc (2 * b) (2 * y + 1)) (Zc (2 * y + 1 + 6 * b)) := by
  induction b with
  | zero => intro y; exact ⟨0, rfl⟩
  | succ b ih =>
    intro y
    have h1 := w_sweep (2 * b) y
    have h2 := ih (y + 3)
    rw [show 2 * b + 2 = 2 * (b + 1) by omega] at h1
    rw [show 2 * (y + 3) + 1 = 2 * y + 7 by omega, show 2 * y + 7 + 6 * b = 2 * y + 1 + 6 * (b + 1) by omega] at h2
    exact (Reaches.of h1).trans h2

theorem w_odd (b : Nat) : ∀ y : Nat, Reaches (Wc (2 * b + 1) (2 * y + 1)) (Zc (2 * y + 6 * b + 6)) := by
  induction b with
  | zero => intro y; exact Reaches.of (w_sweep1 y)
  | succ b ih =>
    intro y
    have h1 := w_sweep (2 * b + 1) y
    have h2 := ih (y + 3)
    rw [show 2 * b + 1 + 2 = 2 * (b + 1) + 1 by omega] at h1
    rw [show 2 * (y + 3) + 1 = 2 * y + 7 by omega, show 2 * (y + 3) + 6 * b + 6 = 2 * y + 6 * (b + 1) + 6 by omega] at h2
    exact (Reaches.of h1).trans h2

theorem w_to_z (x y : Nat) : Reaches (Wc x (2 * y + 1)) (Zc (sweepv x y)) := by
  obtain ⟨b, hb | hb⟩ : ∃ b, x = 2 * b ∨ x = 2 * b + 1 := ⟨x / 2, by omega⟩
  · subst hb
    have e : sweepv (2 * b) y = 2 * y + 1 + 6 * b := by
      unfold sweepv; rw [if_pos (by omega)]; omega
    rw [e]; exact w_even b y
  · subst hb
    have e : sweepv (2 * b + 1) y = 2 * y + 6 * b + 6 := by
      unfold sweepv; rw [if_neg (by omega)]; omega
    rw [e]; exact w_odd b y

/-! ## The rounds of the odd reset -/

/-- The outcome of the rounds. -/
inductive Res where
  | halt
  | z (t : Nat)
  | rs (d : Nat)
  deriving DecidableEq, Repr

/-- The rounds from `Rc (a+1) (2d+1)` (`f` is fuel: `d < f` suffices). -/
def chainF : Nat → Nat → Nat → Res
  | 0, _, _ => .halt
  | f + 1, a, d =>
    if d = 0 then .halt
    else if d < a then .z (sweepv (a - 1 - d) (2 * d + 2))
    else if d = a then .z (4 * a + 4)
    else if d = a + 1 then .rs (2 * a + 3)
    else chainF f (2 * a + 3) (d - a - 2)

/-- What an outcome says about a configuration. -/
def Sem (c : Config) : Res → Prop
  | .halt => Halts trans c
  | .z t => Reach c (Zc t)
  | .rs d => Reach c (Rc 0 (2 * d + 3))

theorem sem_pre {c c' : Config} {r : Res} (h : Reach c c') (h' : Sem c' r) : Sem c r := by
  cases r with
  | halt => exact halts_pre h.reaches h'
  | z t => exact reaches_reach h.reaches h'
  | rs d => exact reaches_reach h.reaches h'

theorem chain_sem (f : Nat) : ∀ a d : Nat, d < f → Sem (Rc (a + 1) (2 * d + 1)) (chainF f a d) := by
  induction f with
  | zero => intro a d h; omega
  | succ f ih =>
    intro a d hd
    unfold chainF
    by_cases h0 : d = 0
    · subst h0; rw [if_pos rfl]; exact r_halt a
    rw [if_neg h0]
    -- every other case starts a round
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have hstart := r_int a (2 * d' + 1)
    rw [show 2 * d' + 1 + 2 = 2 * (d' + 1) + 1 by omega] at hstart
    have hs := Reach.of (n := 2 * a + 7) hstart
    by_cases h1 : d' + 1 < a
    · rw [if_pos h1]
      obtain ⟨e, rfl⟩ : ∃ e, a = d' + 1 + e + 1 := ⟨a - d' - 2, by omega⟩
      have hi := i_iter (d' + 1) (e + 1) 0 1
      rw [show e + 1 + (d' + 1) = d' + 1 + e + 1 by omega, show 1 + 2 * (d' + 1) = 2 * (d' + 1) + 1 by omega,
        show 0 + (d' + 1) = d' + 1 by omega] at hi
      have he := Reaches.of (i_end1 e (d' + 1))
      have hw := w_to_z e (2 * (d' + 1) + 2)
      rw [show 2 * (2 * (d' + 1) + 2) + 1 = 4 * (d' + 1) + 5 by omega] at hw
      rw [show d' + 1 + e + 1 - 1 - (d' + 1) = e by omega]
      exact reach_reaches hs (hi.trans (he.trans hw))
    rw [if_neg h1]
    by_cases h2 : d' + 1 = a
    · rw [if_pos h2]; subst h2
      have hi := i_iter (d' + 1) 0 0 1
      rw [show 0 + (d' + 1) = d' + 1 by omega, show 1 + 2 * (d' + 1) = 2 * (d' + 1) + 1 by omega] at hi
      exact reach_reaches hs (hi.trans (Reaches.of (i_fin1 (d' + 1))))
    rw [if_neg h2]
    by_cases h3 : d' + 1 = a + 1
    · rw [if_pos h3]
      obtain rfl : d' = a := by omega
      have hi := i_iter d' 0 0 3
      rw [show 0 + d' = d' by omega, show 3 + 2 * d' = 2 * (d' + 1) + 1 by omega] at hi
      have h4 := r_restart (2 * d' + 2)
      rw [show 2 * d' + 2 + 1 = 2 * d' + 3 by omega, show 2 * (2 * d' + 2) + 5 = 2 * (2 * d' + 3) + 3 by omega] at h4
      exact reach_reaches hs (hi.trans ((Reaches.of (i_fin3 d')).trans (Reaches.of h4)))
    rw [if_neg h3]
    -- a full round, then the rounds go on from `Rc (2a+4) _`
    have hi := i_iter a 0 0 (2 * (d' + 1 - a - 2) + 1 + 4)
    rw [show 0 + a = a by omega, show 2 * (d' + 1 - a - 2) + 1 + 4 + 2 * a = 2 * (d' + 1) + 1 by omega] at hi
    have hf := i_fin a (2 * (d' + 1 - a - 2) + 1)
    rw [show 2 * a + 4 = (2 * a + 3) + 1 by omega] at hf
    exact sem_pre (reach_reaches hs (hi.trans (Reaches.of hf))) (ih (2 * a + 3) (d' + 1 - a - 2) (by omega))

/-! ## Small blocks, by evaluation -/

theorem app_ones (n : Nat) (s : Tape) : app (List.replicate n true) s = rep n [true] s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, app_cons, ih]; rfl
theorem app_zeros (k : Nat) : app (List.replicate k false) blank = blank := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, app_cons, ih, cons_false_blank]

theorem small_reach {n t t' k : Nat}
    (h : TM.fsteps trans n ⟨List.replicate t true, [], .A⟩ = some ⟨List.replicate t' true ++ List.replicate k false, [], .A⟩) :
    steps n (Zc t) = some (Zc t') := by
  have e := FCfg.steps_eq trans n ⟨List.replicate t true, [], .A⟩
  rw [h] at e
  simp only [Option.map, FCfg.toCfg, app_ones, ← app_app, app_zeros] at e
  exact e

theorem z0 : steps 344 (Zc 0) = some (Zc 19) := small_reach (k := 1) (by decide)
theorem z1 : steps 338 (Zc 1) = some (Zc 19) := small_reach (k := 1) (by decide)
theorem z2 : steps 28 (Zc 2) = some (Zc 6) := small_reach (k := 0) (by decide)
theorem z4 : steps 32 (Zc 4) = some (Zc 7) := small_reach (k := 1) (by decide)
theorem z5 : steps 291 (Zc 5) = some (Zc 20) := small_reach (k := 0) (by decide)
/-- `1^3 A>` halts (124 steps, then the halting transition). -/
theorem z3 : Halts trans (Zc 3) := by
  have h : TM.fsteps trans 124 ⟨List.replicate 3 true, [], .A⟩ =
      some ⟨[false, true, false, true, false, true, false, true, false, true, false, true, false, true, false], [], .D⟩ := by
    decide
  refine ⟨124, FCfg.toCfg ⟨[false, true, false, true, false, true, false, true, false, true, false, true, false, true,
    false], [], .D⟩, ?_, ?_⟩
  · have e := FCfg.steps_eq trans 124 ⟨List.replicate 3 true, [], .A⟩
    rw [h] at e; exact e
  · rw [FCfg.step_eq]; rfl

/-! ## The map -/

/-- The states of the abstract map: `z t` is `1^t A>`, `rs d` is `C> 0 1^(2d+4)` (a restart of the rounds). -/
inductive Node where
  | z (t : Nat)
  | rs (d : Nat)
  deriving DecidableEq, Repr

def Node.cfg : Node → Config
  | .z t => Zc t
  | .rs d => Rc 0 (2 * d + 3)

def Res.node : Res → Option Node
  | .halt => none
  | .z t => some (.z t)
  | .rs d => some (.rs d)

/-- **The reset map.** `none`: the machine halts. -/
def F : Node → Option Node
  | .z t =>
    if t = 3 then none
    else if t = 0 then some (.z 19) else if t = 1 then some (.z 19) else if t = 2 then some (.z 6)
    else if t = 4 then some (.z 7) else if t = 5 then some (.z 20)
    else if t % 2 = 0 then some (.z (sweepv (t / 2 - 2) 3))
    else (chainF ((t + 3) / 2 + 1) 1 ((t + 3) / 2)).node
  | .rs d => (chainF (d + 1) 1 d).node

/-- What `F` says about a state. -/
def FSem (c : Config) : Option Node → Prop
  | none => Halts trans c
  | some s' => Reach c s'.cfg

theorem fsem_res {c : Config} {r : Res} (h : Sem c r) : FSem c r.node := by
  cases r <;> exact h

/-- The rounds from `Rc 0 (2d+3)`. -/
theorem rs_sem (d : Nat) : FSem (Rc 0 (2 * d + 3)) (chainF (d + 1) 1 d).node := by
  have h1 := r_zero (2 * d + 1)
  rw [show 2 * d + 1 + 2 = 2 * d + 3 by omega] at h1
  exact fsem_res (sem_pre (Reach.of h1) (chain_sem (d + 1) 1 d (by omega)))

theorem F_sem (s : Node) : FSem s.cfg (F s) := by
  cases s with
  | rs d => exact rs_sem d
  | z t =>
    show FSem (Zc t) _
    dsimp only [F]
    by_cases h3 : t = 3
    · subst h3; exact z3
    rw [if_neg h3]
    by_cases h0 : t = 0
    · subst h0; exact Reach.of z0
    rw [if_neg h0]
    by_cases h1 : t = 1
    · subst h1; exact Reach.of z1
    rw [if_neg h1]
    by_cases h2 : t = 2
    · subst h2; exact Reach.of z2
    rw [if_neg h2]
    by_cases h4 : t = 4
    · subst h4; exact Reach.of z4
    rw [if_neg h4]
    by_cases h5 : t = 5
    · subst h5; exact Reach.of z5
    rw [if_neg h5]
    by_cases he : t % 2 = 0
    · rw [if_pos he]
      obtain ⟨k, rfl⟩ : ∃ k, t = 2 * k + 6 := ⟨t / 2 - 3, by omega⟩
      have h := z_even k
      have hw := w_to_z (k + 1) 3
      rw [show (2 * k + 6) / 2 - 2 = k + 1 by omega]
      exact reach_reaches (Reach.of (n := 4 * k + 35) h) hw
    · rw [if_neg he]
      obtain ⟨k, rfl⟩ : ∃ k, t = 2 * k + 7 := ⟨(t - 7) / 2, by omega⟩
      have h := z_odd k
      have e : (2 * k + 7 + 3) / 2 = k + 5 := by omega
      rw [e]
      have hr := rs_sem (k + 5)
      rw [show 2 * (k + 5) + 3 = 2 * k + 13 by omega] at hr
      cases hc : (chainF (k + 5 + 1) 1 (k + 5)).node with
      | none => rw [hc] at hr; exact halts_pre (Reaches.of h) hr
      | some s' => rw [hc] at hr; exact reaches_reach (Reaches.of h) hr

/-! ## Halting is the orbit question -/

/-- The orbit of `s` under `F`, `none` once it has hit a halting state. -/
def orbitFrom (s : Node) : Nat → Option Node
  | 0 => some s
  | n + 1 => (F s).bind (fun s' => orbitFrom s' n)

theorem runs_long (N : Nat) : ∀ s : Node, (∀ n, orbitFrom s n ≠ none) →
    ∃ m, N ≤ m ∧ ∃ c, steps m s.cfg = some c := by
  induction N with
  | zero => intro s _; exact ⟨0, Nat.le_refl 0, _, rfl⟩
  | succ N ih =>
    intro s hs
    cases hF : F s with
    | none => exact absurd (by simp [orbitFrom, hF]) (hs 1)
    | some s' =>
      have hs' : ∀ n, orbitFrom s' n ≠ none := fun n h => hs (n + 1) (by simp [orbitFrom, hF, h])
      obtain ⟨m, hm, c, hc⟩ := ih s' hs'
      have hr := F_sem s
      rw [hF] at hr
      obtain ⟨k, hk⟩ := hr
      exact ⟨k + 1 + m, by omega, c, steps_seq trans hk hc⟩

/-- **The machine halts from the state `s` iff the orbit of `s` under `F` reaches `none`.** -/
theorem halts_from (s : Node) : Halts trans s.cfg ↔ ∃ n, orbitFrom s n = none := by
  constructor
  · intro hh
    refine Classical.byContradiction fun hne => ?_
    have hs : ∀ n, orbitFrom s n ≠ none := fun n h => hne ⟨n, h⟩
    refine not_halts_of_forall trans ?_ hh
    exact forall_of_unbounded trans (fun m => ∃ c, steps m s.cfg = some c) (runs_long · s hs) (fun _ h => h)
  · rintro ⟨n, hn⟩
    induction n generalizing s with
    | zero => simp [orbitFrom] at hn
    | succ n ih =>
      have hr := F_sem s
      cases hF : F s with
      | none => rw [hF] at hr; exact hr
      | some s' =>
        rw [hF] at hr
        have hn' : orbitFrom s' n = none := by simpa [orbitFrom, hF] using hn
        exact halts_pre hr.reaches (ih s' hn')

/-- **Main theorem.** The machine halts from blank tape iff the orbit of `z 0` (blank tape) under `F` reaches
`none`. -/
theorem halts_iff : HaltsFromBlank ↔ ∃ n, orbitFrom (.z 0) n = none := halts_from (.z 0)

theorem F_0 : F (.z 0) = some (.z 19) := by decide
theorem F_19 : F (.z 19) = some (.z 44) := by decide

/-- The same from `1^44 A>`, the first reset after the two short ones: blank tape → `1^19` → `1^44`. -/
theorem halts_iff_44 : HaltsFromBlank ↔ ∃ n, orbitFrom (.z 44) n = none := by
  rw [halts_iff]
  have shift : ∀ n, orbitFrom (.z 0) (n + 2) = orbitFrom (.z 44) n := fun n => by
    simp [orbitFrom, F_0, F_19]
  constructor
  · rintro ⟨n, hn⟩
    match n, hn with
    | 0, hn => simp [orbitFrom] at hn
    | 1, hn => simp [orbitFrom, F_0] at hn
    | n + 2, hn => exact ⟨n, by rw [← shift]; exact hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 2, by rw [shift]; exact hn⟩

/-! ## Which states halt: a closed form

The rounds from `Rc (a+1) (2d+1)` halt iff `d + s + (a+3) = 2^s (a+3)` for some `s` (the number of full rounds);
from a reset (`a = 1`) this is `t + 2s + 11 = 2^(s+3)` for the block `1^t`, i.e. `t = 2^(j+1) - 2j - 7` with
`j = s + 2`: t = 3, 17, 47, 109, 235, ... -/

/-- The rounds from `Rc (a+1) (2d+1)` halt. -/
def HaltP (a d : Nat) : Prop := ∃ s, d + s + (a + 3) = 2 ^ s * (a + 3)

theorem pow_key (s a : Nat) : 2 ^ (s + 1) * (a + 3) = 2 ^ s * (2 * a + 3 + 3) := by
  rw [Nat.pow_succ, Nat.mul_assoc]; congr 1

theorem not_haltP_small {a d : Nat} (h0 : d ≠ 0) (hle : d ≤ a + 1) : ¬ HaltP a d := by
  rintro ⟨s, hs⟩
  cases s with
  | zero => simp at hs; omega
  | succ s =>
    have hP : s + 1 < 2 ^ (s + 1) := Nat.lt_two_pow_self
    have h2 : 2 * a ≤ 2 ^ (s + 1) * a := Nat.mul_le_mul_right a (by omega)
    rw [Nat.mul_add] at hs
    omega

theorem chain_halt (f : Nat) : ∀ a d : Nat, d < f → (chainF f a d = .halt ↔ HaltP a d) := by
  induction f with
  | zero => intro a d h; omega
  | succ f ih =>
    intro a d hd
    unfold chainF
    by_cases h0 : d = 0
    · subst h0; rw [if_pos rfl]; exact ⟨fun _ => ⟨0, by simp⟩, fun _ => rfl⟩
    rw [if_neg h0]
    by_cases h1 : d < a
    · rw [if_pos h1]; exact ⟨fun h => (by cases h), fun h => absurd h (not_haltP_small h0 (by omega))⟩
    rw [if_neg h1]
    by_cases h2 : d = a
    · rw [if_pos h2]; exact ⟨fun h => (by cases h), fun h => absurd h (not_haltP_small h0 (by omega))⟩
    rw [if_neg h2]
    by_cases h3 : d = a + 1
    · rw [if_pos h3]; exact ⟨fun h => (by cases h), fun h => absurd h (not_haltP_small h0 (by omega))⟩
    rw [if_neg h3, ih (2 * a + 3) (d - a - 2) (by omega)]
    constructor
    · rintro ⟨s, hs⟩; exact ⟨s + 1, by rw [pow_key]; omega⟩
    · rintro ⟨s, hs⟩
      cases s with
      | zero => simp at hs; omega
      | succ s => exact ⟨s, by rw [pow_key] at hs; omega⟩

theorem node_none {r : Res} : r.node = none ↔ r = .halt := by
  cases r <;> simp [Res.node]

/-- A restart state halts iff `d + s + 4 = 2^(s+2)` for some `s`. -/
theorem F_rs_none (d : Nat) : F (.rs d) = none ↔ ∃ s, d + s + 4 = 2 ^ (s + 2) := by
  show (chainF (d + 1) 1 d).node = none ↔ _
  rw [node_none, chain_halt (d + 1) 1 d (by omega)]
  constructor
  · rintro ⟨s, hs⟩; exact ⟨s, by rw [Nat.pow_add]; simpa using hs⟩
  · rintro ⟨s, hs⟩; exact ⟨s, by rw [Nat.pow_add] at hs; simpa using hs⟩

/-- **The halting blocks.** `F (z t) = none` iff `t + 2s + 11 = 2^(s+3)` for some `s`, i.e.
`t = 2^(j+1) - 2j - 7` (j ≥ 3): t = 3, 17, 47, 109, 235, 489, ... -/
theorem F_z_none (t : Nat) : F (.z t) = none ↔ ∃ s, t + 2 * s + 11 = 2 ^ (s + 3) := by
  have par : ∀ s, 2 ^ (s + 3) = 8 * 2 ^ s := fun s => by rw [Nat.pow_add]; omega
  have big : ∀ s, s < 2 ^ s := fun s => Nat.lt_two_pow_self
  dsimp only [F]
  by_cases h3 : t = 3
  · subst h3; simp only [if_pos rfl]; exact ⟨fun _ => ⟨1, by decide⟩, fun _ => rfl⟩
  rw [if_neg h3]
  have small : t ≤ 5 → ¬ ∃ s, t + 2 * s + 11 = 2 ^ (s + 3) := by
    rintro ht ⟨s, hs⟩
    rw [par] at hs
    have := big s
    cases s with
    | zero => simp at hs
    | succ s =>
      cases s with
      | zero => simp at hs; omega
      | succ s => have := big s; rw [Nat.pow_succ, Nat.pow_succ] at hs; omega
  by_cases h0 : t = 0
  · rw [if_pos h0]; exact ⟨fun h => (by cases h), fun h => absurd h (small (by omega))⟩
  rw [if_neg h0]
  by_cases h1 : t = 1
  · rw [if_pos h1]; exact ⟨fun h => (by cases h), fun h => absurd h (small (by omega))⟩
  rw [if_neg h1]
  by_cases h2 : t = 2
  · rw [if_pos h2]; exact ⟨fun h => (by cases h), fun h => absurd h (small (by omega))⟩
  rw [if_neg h2]
  by_cases h4 : t = 4
  · rw [if_pos h4]; exact ⟨fun h => (by cases h), fun h => absurd h (small (by omega))⟩
  rw [if_neg h4]
  by_cases h5 : t = 5
  · rw [if_pos h5]; exact ⟨fun h => (by cases h), fun h => absurd h (small (by omega))⟩
  rw [if_neg h5]
  by_cases he : t % 2 = 0
  · rw [if_pos he]
    refine ⟨fun h => (by cases h), ?_⟩
    rintro ⟨s, hs⟩; rw [par] at hs; omega
  · rw [if_neg he, node_none, chain_halt _ 1 _ (by omega)]
    constructor
    · rintro ⟨s, hs⟩; exact ⟨s, by rw [par]; omega⟩
    · rintro ⟨s, hs⟩; exact ⟨s, by rw [par] at hs; omega⟩

/-- The halting states of the map. -/
def InH : Node → Prop
  | .z t => ∃ s, t + 2 * s + 11 = 2 ^ (s + 3)
  | .rs d => ∃ s, d + s + 4 = 2 ^ (s + 2)

theorem F_none_iff (s : Node) : F s = none ↔ InH s := by
  cases s with
  | z t => exact F_z_none t
  | rs d => exact F_rs_none d

theorem orbit_succ (n : Nat) : ∀ s : Node, orbitFrom s (n + 1) = (orbitFrom s n).bind F := by
  induction n with
  | zero => intro s; simp [orbitFrom]
  | succ n ih =>
    intro s
    show (F s).bind (fun s' => orbitFrom s' (n + 1)) = ((F s).bind (fun s' => orbitFrom s' n)).bind F
    cases F s with
    | none => rfl
    | some s' => exact ih s'

theorem orbit_none_iff (s : Node) : (∃ n, orbitFrom s n = none) ↔ ∃ n s', orbitFrom s n = some s' ∧ InH s' := by
  constructor
  · rintro ⟨n, hn⟩
    induction n with
    | zero => simp [orbitFrom] at hn
    | succ n ih =>
      rw [orbit_succ] at hn
      cases ho : orbitFrom s n with
      | none => exact ih ho
      | some s' =>
        rw [ho] at hn
        exact ⟨n, s', ho, (F_none_iff s').1 hn⟩
  · rintro ⟨n, s', hn, hH⟩
    exact ⟨n + 1, by rw [orbit_succ, hn]; exact (F_none_iff s').2 hH⟩

/-- **The machine halts from blank tape iff the orbit of `1^44` under `F` hits a halting state**: a block
`1^t` with `t = 2^(j+1) - 2j - 7` (written `t + 2s + 11 = 2^(s+3)`), or a restart `rs d` with
`d + s + 4 = 2^(s+2)`. -/
theorem halts_iff_H : HaltsFromBlank ↔ ∃ n s, orbitFrom (.z 44) n = some s ∧ InH s := by
  rw [halts_iff_44, orbit_none_iff]

end H165234
