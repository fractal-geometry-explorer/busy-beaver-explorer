import Doubling
import Overflow

/-!
# The return map of 1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA, proved

Configurations (tapes left to right, the head reads the cell after `S>`; `R01` is the tail `0 1 0^inf`):

* `S x`     = `0^inf 1^x 1 1 1 0 B> 0^inf`                      (the reset configuration, `Doubling.lean`)
* `Pc k m`  = `0^inf F> 0 0 (10)^k 1^m 0 1 0^inf`                (a doubling round's start)
* `Qc u n`  = `0^inf F> 0 0 (10)^3 (1110)^u 1^n 0 1 0^inf`
* `Tc u v`  = `0^inf F> 0 0 (10)^3 (1110)^u 1111 0 (10)^v 0 1 0^inf`
* `Oc p i r` = `0^inf 1^6 0 (10)^p (1111)^i F> 1 0 1^r 0 1 0^inf` (a doubling round that ran out of ones, r < 2)

The doubling rounds are in `Doubling.lean`, the overflow rules in `Overflow.lean` (generated). This file restates
the rules on these configurations and assembles them into a map `F` on the nodes `s x` (= `S (x+6)`),
`p a m` (= `Pc (a+3) m`), `q u c` (= `Qc (u+1) (2c+1)`) and `t u v` (= `Tc u (v+1)`).

Main results:
* `F_sem`: `F s = some s'` → the machine goes from `s` to `s'` (at least one step); `F s = none` → it halts from `s`;
* `halts_iff`: **the machine halts from blank tape iff the orbit of `s 7` (= `S 13`) under `F` reaches `none`**;
* `halts_iff_H`: the same, with the halting nodes named: the orbit hits a node `p a 0` (a doubling round that
  starts with no ones at all).
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace H90097

open TM

/-! ## Tape identities -/

theorem t_quad (n : Nat) (s : Tape) : rep n [true, true, true, true] s = rep (4 * n) [true] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show app [true, true, true, true] (rep n [true, true, true, true] s) = rep (4 * n + 1 + 1 + 1 + 1) [true] s
    rw [ih]; rfl
theorem t_two (n : Nat) (s : Tape) : rep n [true, true] s = rep (2 * n) [true] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show app [true, true] (rep n [true, true] s) = rep (2 * n + 1 + 1) [true] s
    rw [ih]; rfl
theorem t_ftft (n : Nat) (s : Tape) : rep n [false, true, false, true] s = rep (2 * n) [false, true] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show app [false, true, false, true] (rep n [false, true, false, true] s) = rep (2 * n + 1 + 1) [false, true] s
    rw [ih]; rfl
theorem t_ones (n : Nat) (s : Tape) : rep n [true] (cons true s) = rep (n + 1) [true] s :=
  rep_app_comm n [true] s
theorem t_ones_ones (a b : Nat) (s : Tape) : rep a [true] (rep b [true] s) = rep (a + b) [true] s :=
  (rep_add a b [true] s).symm
theorem t_tf (n : Nat) (s : Tape) : rep n [true, false] (cons true (cons false s)) = rep (n + 1) [true, false] s :=
  rep_app_comm n [true, false] s
theorem t_ft (n : Nat) (s : Tape) : rep n [false, true] (cons false (cons true s)) = rep (n + 1) [false, true] s :=
  rep_app_comm n [false, true] s
theorem t_tttf (n : Nat) (s : Tape) :
    rep n [true, true, true, false] (cons true (cons true (cons true (cons false s)))) = rep (n + 1) [true, true, true, false] s :=
  rep_app_comm n [true, true, true, false] s
theorem t_rot3 (n : Nat) (s : Tape) :
    cons true (cons true (cons true (rep n [false, true, true, true] s))) =
      rep n [true, true, true, false] (cons true (cons true (cons true s))) :=
  rep_rotate n [true, true, true] [false, true, true, true] [true, true, true, false] rfl s
theorem t_rot2 (n : Nat) (s : Tape) :
    cons true (cons true (rep n [true, false, true, true] s)) = rep n [true, true, true, false] (cons true (cons true s)) :=
  rep_rotate n [true, true] [true, false, true, true] [true, true, true, false] rfl s
theorem t_ft_tf (n : Nat) (s : Tape) : rep n [false, true] (cons false s) = cons false (rep n [true, false] s) :=
  (rep_rotate n [false] [true, false] [false, true] rfl s).symm
theorem t_ft_odd (q : Nat) (s : Tape) :
    rep (2 * q + 1) [false, true] s = cons false (cons true (rep q [false, true, false, true] s)) := by
  rw [t_ftft]; rfl
theorem t_ft_even (q : Nat) (s : Tape) :
    rep (2 * q + 2) [false, true] s = cons false (cons true (cons false (cons true (rep q [false, true, false, true] s)))) := by
  rw [t_ftft]; rfl
theorem t_tf_odd (b : Nat) (s : Tape) :
    rep (2 * b + 3) [true, false] s = cons true (cons false (rep (b + 1) [true, false, true, false] s)) := by
  rw [dquads]; rfl
theorem t_tf_even (b : Nat) (s : Tape) :
    rep (2 * b + 4) [true, false] s = rep (b + 2) [true, false, true, false] s := by
  rw [dquads]; rfl

theorem f_one (n : Nat) (s : Tape) : cons true (rep n [true] s) = rep (n + 1) [true] s := rfl
theorem f_tf (n : Nat) (s : Tape) : cons true (cons false (rep n [true, false] s)) = rep (n + 1) [true, false] s := rfl
theorem f_ft (n : Nat) (s : Tape) : cons false (cons true (rep n [false, true] s)) = rep (n + 1) [false, true] s := rfl
theorem f_tttf (n : Nat) (s : Tape) :
    cons true (cons true (cons true (cons false (rep n [true, true, true, false] s)))) = rep (n + 1) [true, true, true, false] s := rfl
theorem m_tf (a b : Nat) (s : Tape) : rep a [true, false] (rep b [true, false] s) = rep (a + b) [true, false] s :=
  (rep_add a b _ s).symm
theorem m_ft (a b : Nat) (s : Tape) : rep a [false, true] (rep b [false, true] s) = rep (a + b) [false, true] s :=
  (rep_add a b _ s).symm
theorem m_tttf (a b : Nat) (s : Tape) :
    rep a [true, true, true, false] (rep b [true, true, true, false] s) = rep (a + b) [true, true, true, false] s :=
  (rep_add a b _ s).symm
theorem o_one (s : Tape) : cons true s = rep 1 [true] s := rfl

/-- The tape normalisation used below: blocks of ones become `rep _ [true]`, pairs `rep _ [true, false]` and
`rep _ [false, true]`, blocks `1110` `rep _ [true, true, true, false]`, with literal copies next to a block folded
into it and the counts in a normal form. -/
macro "tnormA" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [t_quad, t_two, t_ftft, dquads, t_rot3, t_rot2] $[$loc]?)
macro "tnormB" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [t_ones, t_ones_ones, t_tf, t_ft, t_tttf, f_one, f_tf, f_ft, f_tttf, m_tf, m_ft, m_tttf, rep_zero, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul] $[$loc]?)
macro "tnorm" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| ((try tnormA $[$loc]?); (try tnormB $[$loc]?)))


/-! ## The configurations -/

/-- The tail `0 1 0^inf`. -/
def R01 : Tape := cons false (cons true blank)
/-- `0^inf F> 0 0 (10)^k 1^m 0 1 0^inf`. -/
abbrev Pc (k m : Nat) : Config := P k m R01
/-- `0^inf F> 0 0 (10)^3 (1110)^u 1^n 0 1 0^inf`. -/
def Qc (u n : Nat) : Config :=
  ⟨blank, cons false (cons false (rep 3 [true, false] (rep u [true, true, true, false] (rep n [true] R01)))), .F⟩
/-- `0^inf F> 0 0 (10)^3 (1110)^u 1111 0 (10)^v 0 1 0^inf`. -/
def Tc (u v : Nat) : Config :=
  ⟨blank, cons false (cons false (rep 3 [true, false] (rep u [true, true, true, false]
    (rep 4 [true] (cons false (rep v [true, false] R01)))))), .F⟩
/-- The wall `1^6 0` (left of the head, nearest cell first). -/
def W6 : Tape := cons false (cons true (cons true (cons true (cons true (cons true (cons true blank))))))
/-- `0^inf 1^6 0 (10)^p (1111)^i F> 1 0 1^r 0 1 0^inf`. -/
def Oc (p i r : Nat) : Config :=
  ⟨rep i [true, true, true, true] (rep p [false, true] W6), cons true (cons false (rep r [true] R01)), .F⟩

/-- Unfold the named configurations. -/
macro "cfgs" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Oc, Pc, P, Qc, Tc, S, R01, W6, rep_zero, rep_succ, app_cons, app_nil] $[$loc]?)

/-! ## Reaching -/

/-- `c` reaches `c'` in at least one step. -/
def Reach (c c' : Config) : Prop := ∃ n, steps (n + 1) c = some c'
/-- `c` reaches `c'` (possibly in no step). -/
def Reaches (c c' : Config) : Prop := ∃ n, steps n c = some c'

theorem Reaches.trans {a b c : Config} : Reaches a b → Reaches b c → Reaches a c
  | ⟨n, h1⟩, ⟨m, h2⟩ => ⟨n + m, steps_seq H90097.trans h1 h2⟩
theorem reach_reaches {a b c : Config} : Reach a b → Reaches b c → Reach a c
  | ⟨n, h1⟩, ⟨m, h2⟩ => ⟨n + m, steps_congr trans (by omega) (steps_seq trans h1 h2)⟩
theorem reaches_reach {a b c : Config} : Reaches a b → Reach b c → Reach a c
  | ⟨n, h1⟩, ⟨m, h2⟩ => ⟨n + m, steps_congr trans (by omega) (steps_seq trans h1 h2)⟩
theorem Reach.reaches {a b : Config} : Reach a b → Reaches a b
  | ⟨n, h⟩ => ⟨n + 1, h⟩
theorem halts_pre {a b : Config} : Reaches a b → Halts trans b → Halts trans a
  | ⟨n, h1⟩, ⟨m, c, h2, h3⟩ => ⟨n + m, c, steps_seq trans h1 h2, h3⟩
/-- A run of a positive number of steps is a `Reach`. -/
theorem reach_of {n : Nat} {c c' : Config} (h : steps n c = some c') (hn : 0 < n) : Reach c c' :=
  ⟨n - 1, by rw [show n - 1 + 1 = n by omega]; exact h⟩

/-! ## The overflow rules on these configurations -/

/-- A run between two configurations equal to the named ones. -/
theorem reach_of' {n : Nat} {c c' d d' : Config} (h : steps n d = some d') (e1 : c = d) (e2 : c' = d') (hn : 0 < n) :
    Reach c c' := by
  subst e1; subst e2; exact reach_of h hn

/-- Restate a generated rule on the named configurations. -/
macro "rule" h:term : tactic => `(tactic| (refine reach_of' $h ?_ ?_ (by omega) <;> ((try cfgs) <;> tnorm <;> (try simp only [Nat.add_comm, Nat.add_left_comm]))))

theorem r_odd0 (q i : Nat) : Reach (Oc (2 * q + 1) i 0) (Pc (2 * q + 6) (4 * i + 2)) := by rule o_odd0 i q
theorem r_odd1 (q i : Nat) : Reach (Oc (2 * q + 1) i 1) (Tc q (2 * i + 3)) := by
  refine reach_of' (o_odd1 i q) ?_ ?_ (by omega) <;> (cfgs; tnorm) ; simp only [t_ft_tf]; tnorm
theorem r_even0 (q i : Nat) : Reach (Oc (2 * q + 2) i 0) (Qc (q + 1) (4 * i + 7)) := by rule o_even0 i q
theorem r_even1 (q i : Nat) : Reach (Oc (2 * q + 2) i 1) (S (4 * q + 4 * i + 17)) := by rule o_even1 i q
theorem r_zero0 (i : Nat) : Reach (Oc 0 i 0) (S (4 * i + 7)) := by rule o_zero0 i
theorem r_zero1 (i : Nat) : Reach (Oc 0 i 1) (S (4 * i + 13)) := by rule o_zero1 i
theorem r_p1o (b : Nat) : Reach (Pc (2 * b + 3) 1) (S (4 * b + 13)) := by rule p1_odd b
theorem r_p1e (b : Nat) : Reach (Pc (2 * b + 4) 1) (Qc (b + 2) 3) := by rule p1_even b
theorem r_p2o (b : Nat) : Reach (Pc (2 * b + 3) 2) (Tc (b + 1) 1) := by rule p2_odd b
theorem r_p2e (b : Nat) : Reach (Pc (2 * b + 4) 2) (S (4 * b + 17)) := by rule p2_even b
theorem r_qbig (u c : Nat) : Reach (Qc (u + 1) (c + 9)) (Pc (2 * u + 11) c) := by rule q_big c u
theorem r_q1 (u : Nat) : Reach (Qc (u + 1) 1) (S (4 * u + 17)) := by rule q1 u
theorem r_q3 (u : Nat) : Reach (Qc (u + 1) 3) (Qc 1 (4 * u + 11)) := by rule q3 u
theorem r_q5 (u : Nat) : Reach (Qc (u + 1) 5) (Pc 6 (4 * u + 10)) := by rule q5 u
theorem r_q7 (u : Nat) : Reach (Qc (u + 1) 7) (S (4 * u + 19)) := by rule q7 u
theorem r_t (u v : Nat) : Reach (Tc u (v + 1)) (Qc 1 (4 * u + 2 * v + 11)) := by rule t_rule u v
theorem r_S (x : Nat) : Reach (S (x + 6)) (Pc 3 (x + 6)) := by rule reset_start x

/-- `P (j+1) 0`: no ones at all; the machine halts (D reads 1). -/
theorem r_p0 (j : Nat) : Halts trans (Pc (j + 1) 0) := ⟨2 * j + 15, _, p0 j, rfl⟩

/-! ## The doubling round and the start of an overflow -/

/-- A doubling round (as `double` in `Doubling.lean`, with the step count kept positive). -/
theorem r_double (k m : Nat) (hk : 2 ≤ k) (hm : 2 * k + 3 ≤ m) :
    Reach (Pc k m) (Pc (2 * k + 3) (m - (2 * k + 3))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 * j + 7 := ⟨m - (2 * j + 7), by omega⟩
  rw [show 2 * (j + 2) + 3 = 2 * j + 7 by omega, show m' + 2 * j + 7 - (2 * j + 7) = m' by omega]
  have h1 := dbl_intro j (m' + 2 * j + 1) R01
  have e0 : m' + 2 * j + 1 + 6 = m' + 2 * j + 7 := by omega
  rw [e0] at h1
  have rot : cons false (rep (j + 1) [true, false] (cons true (cons true (cons true (cons true (cons true (cons true blank)))))))
      = rep 0 [true, true, true, true] (rep (0 + (j + 1)) [false, true]
          (cons false (cons true (cons true (cons true (cons true (cons true (cons true blank)))))))) := by
    rw [Nat.zero_add]
    exact rep_rotate (j + 1) [false] [true, false] [false, true] rfl _
  rw [rot] at h1
  have e1 : m' + 2 * j + 1 + 3 = (m' + 2) + 2 * (j + 1) := by omega
  rw [e1] at h1
  obtain ⟨t2, h2⟩ := zigs (j + 1) 0 0 (m' + 2) (cons false (cons true (cons true (cons true (cons true (cons true
    (cons true blank))))))) R01
  rw [Nat.zero_add] at h1 h2
  have h3 := dbl_end (j + 1) m' R01
  have e3 : cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false
      (rep (j + 1) [true, false, true, false] (cons true (cons false (rep m' [true] R01)))))))))))
      = rep (2 * j + 7) [true, false] (rep m' [true] R01) := by
    rw [dquads, pairs_cons]
    have : 2 * (j + 1) + 1 + 4 = 2 * j + 7 := by omega
    rw [← this]; rfl
  rw [e3] at h3
  exact reach_of (steps_seq trans h1 (steps_seq trans h2 h3)) (by omega)

/-- **The start of an overflow.** A round of `Pc (j+2) (r + 2z + 3)` (r < 2, z ≤ j + 1): the wall, then z zigs; the
ones run out with `j + 1 − z` pairs left. -/
theorem r_over (j z r : Nat) (hz : z ≤ j + 1) : Reach (Pc (j + 2) (r + 2 * z + 3)) (Oc (j + 1 - z) z r) := by
  have h1 := intro3 j (r + 2 * z) R01
  have e : cons false (cons true (rep (j + 1) [false, true] (cons true (cons true (cons true (cons true (cons true blank)))))))
      = rep 0 [true, true, true, true] (rep ((j + 1 - z) + z) [false, true] W6) := by
    rw [show j + 1 - z + z = j + 1 by omega]
    exact rep_rotate (j + 1) [false, true] [false, true] [false, true] rfl _
  rw [e] at h1
  obtain ⟨t2, h2⟩ := zigs z 0 (j + 1 - z) r W6 R01
  rw [Nat.zero_add] at h2
  exact reach_of (steps_seq trans h1 h2) (by omega)

/-! ## The map -/

/-- The nodes of the map: `s x` is `S (x+6)`, `p a m` is `Pc (a+3) m`, `q u c` is `Qc (u+1) (2c+1)`, `t u v` is
`Tc u (v+1)`. -/
inductive Node where
  | s (x : Nat)
  | p (a m : Nat)
  | q (u c : Nat)
  | t (u v : Nat)
  deriving DecidableEq, Repr

def Node.cfg : Node → Config
  | .s x => S (x + 6)
  | .p a m => Pc (a + 3) m
  | .q u c => Qc (u + 1) (2 * c + 1)
  | .t u v => Tc u (v + 1)

/-- The end of an overflow `Oc pp z r` (pp pairs left, z zigs done, r ones left): which node comes next. -/
def overflow (pp z r : Nat) : Node :=
  if pp = 0 then (if r = 0 then .s (4 * z + 1) else .s (4 * z + 7))
  else if pp % 2 = 1 then (if r = 0 then .p (2 * (pp / 2) + 3) (4 * z + 2) else .t (pp / 2) (2 * z + 2))
  else (if r = 0 then .q (pp / 2 - 1) (2 * z + 3) else .s (4 * (pp / 2 - 1) + 4 * z + 11))

/-- **The map.** `none`: the machine halts. -/
def F : Node → Option Node
  | .s x => some (.p 0 (x + 6))
  | .p a m =>
    if 2 * a + 9 ≤ m then some (.p (2 * a + 6) (m - (2 * a + 9)))
    else if m = 0 then none
    else if m = 1 then (if a % 2 = 0 then some (.s (2 * a + 7)) else some (.q (a / 2 + 1) 1))
    else if m = 2 then (if a % 2 = 0 then some (.t (a / 2 + 1) 0) else some (.s (2 * a + 9)))
    else some (overflow (a + 2 - (m - 3) / 2) ((m - 3) / 2) ((m - 3) % 2))
  | .q u c =>
    if 4 ≤ c then some (.p (2 * u + 8) (2 * c - 8))
    else if c = 0 then some (.s (4 * u + 11))
    else if c = 1 then some (.q 0 (2 * u + 5))
    else if c = 2 then some (.p 3 (4 * u + 10))
    else some (.s (4 * u + 13))
  | .t u v => some (.q 0 (2 * u + v + 5))

/-- What `F` says about a configuration. -/
def FSem (c : Config) : Option Node → Prop
  | none => Halts trans c
  | some s' => Reach c s'.cfg

theorem overflow_sem (pp z r : Nat) (hr : r < 2) : Reach (Oc pp z r) (overflow pp z r).cfg := by
  unfold overflow
  by_cases h0 : pp = 0
  · subst h0; rw [if_pos rfl]
    by_cases hr0 : r = 0
    · subst hr0; rw [if_pos rfl]; show Reach _ (S (4 * z + 1 + 6)); exact r_zero0 z
    · obtain rfl : r = 1 := by omega
      rw [if_neg (by omega)]; show Reach _ (S (4 * z + 7 + 6)); exact r_zero1 z
  rw [if_neg h0]
  by_cases ho : pp % 2 = 1
  · rw [if_pos ho]
    obtain ⟨q, rfl⟩ : ∃ q, pp = 2 * q + 1 := ⟨pp / 2, by omega⟩
    rw [show (2 * q + 1) / 2 = q by omega]
    by_cases hr0 : r = 0
    · subst hr0; rw [if_pos rfl]; show Reach _ (Pc (2 * q + 3 + 3) (4 * z + 2)); exact r_odd0 q z
    · obtain rfl : r = 1 := by omega
      rw [if_neg (by omega)]; show Reach _ (Tc q (2 * z + 2 + 1)); exact r_odd1 q z
  · rw [if_neg ho]
    obtain ⟨q, rfl⟩ : ∃ q, pp = 2 * q + 2 := ⟨pp / 2 - 1, by omega⟩
    rw [show (2 * q + 2) / 2 - 1 = q by omega]
    by_cases hr0 : r = 0
    · subst hr0; rw [if_pos rfl]; show Reach _ (Qc (q + 1) (2 * (2 * z + 3) + 1))
      rw [show 2 * (2 * z + 3) + 1 = 4 * z + 7 by omega]; exact r_even0 q z
    · obtain rfl : r = 1 := by omega
      rw [if_neg (by omega)]; show Reach _ (S (4 * q + 4 * z + 11 + 6))
      rw [show 4 * q + 4 * z + 11 + 6 = 4 * q + 4 * z + 17 by omega]; exact r_even1 q z

theorem F_sem (n : Node) : FSem n.cfg (F n) := by
  cases n with
  | s x => exact r_S x
  | t u v =>
    show Reach (Tc u (v + 1)) (Qc (0 + 1) (2 * (2 * u + v + 5) + 1))
    rw [show 2 * (2 * u + v + 5) + 1 = 4 * u + 2 * v + 11 by omega]; exact r_t u v
  | q u c =>
    show FSem (Qc (u + 1) (2 * c + 1)) _
    dsimp only [F]
    by_cases h4 : 4 ≤ c
    · rw [if_pos h4]
      obtain ⟨d, rfl⟩ : ∃ d, c = d + 4 := ⟨c - 4, by omega⟩
      show Reach _ (Pc (2 * u + 8 + 3) (2 * (d + 4) - 8))
      rw [show 2 * (d + 4) + 1 = 2 * d + 9 by omega, show 2 * u + 8 + 3 = 2 * u + 11 by omega,
        show 2 * (d + 4) - 8 = 2 * d by omega]
      exact r_qbig u (2 * d)
    rw [if_neg h4]
    by_cases h0 : c = 0
    · subst h0; rw [if_pos rfl]; show Reach _ (S (4 * u + 11 + 6)); exact r_q1 u
    rw [if_neg h0]
    by_cases h1 : c = 1
    · subst h1; rw [if_pos rfl]; show Reach _ (Qc (0 + 1) (2 * (2 * u + 5) + 1))
      rw [show 2 * (2 * u + 5) + 1 = 4 * u + 11 by omega]; exact r_q3 u
    rw [if_neg h1]
    by_cases h2 : c = 2
    · subst h2; rw [if_pos rfl]; exact r_q5 u
    rw [if_neg h2]
    obtain rfl : c = 3 := by omega
    show Reach _ (S (4 * u + 13 + 6)); exact r_q7 u
  | p a m =>
    show FSem (Pc (a + 3) m) _
    dsimp only [F]
    by_cases hd : 2 * a + 9 ≤ m
    · rw [if_pos hd]
      have h := r_double (a + 3) m (by omega) (by omega)
      rw [show 2 * (a + 3) + 3 = 2 * a + 6 + 3 by omega, show m - (2 * a + 6 + 3) = m - (2 * a + 9) by omega] at h
      exact h
    rw [if_neg hd]
    by_cases h0 : m = 0
    · subst h0; rw [if_pos rfl]; exact r_p0 (a + 2)
    rw [if_neg h0]
    by_cases h1 : m = 1
    · subst h1; rw [if_pos rfl]
      by_cases ha : a % 2 = 0
      · rw [if_pos ha]
        obtain ⟨b, rfl⟩ : ∃ b, a = 2 * b := ⟨a / 2, by omega⟩
        show Reach (Pc (2 * b + 3) 1) (S (2 * (2 * b) + 7 + 6))
        rw [show 2 * (2 * b) + 7 + 6 = 4 * b + 13 by omega]; exact r_p1o b
      · rw [if_neg ha]
        obtain ⟨b, rfl⟩ : ∃ b, a = 2 * b + 1 := ⟨a / 2, by omega⟩
        show Reach (Pc (2 * b + 1 + 3) 1) (Qc ((2 * b + 1) / 2 + 1 + 1) (2 * 1 + 1))
        rw [show 2 * b + 1 + 3 = 2 * b + 4 by omega, show (2 * b + 1) / 2 + 1 + 1 = b + 2 by omega]; exact r_p1e b
    rw [if_neg h1]
    by_cases h2 : m = 2
    · subst h2; rw [if_pos rfl]
      by_cases ha : a % 2 = 0
      · rw [if_pos ha]
        obtain ⟨b, rfl⟩ : ∃ b, a = 2 * b := ⟨a / 2, by omega⟩
        show Reach (Pc (2 * b + 3) 2) (Tc (2 * b / 2 + 1) (0 + 1))
        rw [show 2 * b / 2 = b by omega]; exact r_p2o b
      · rw [if_neg ha]
        obtain ⟨b, rfl⟩ : ∃ b, a = 2 * b + 1 := ⟨a / 2, by omega⟩
        show Reach (Pc (2 * b + 1 + 3) 2) (S (2 * (2 * b + 1) + 9 + 6))
        rw [show 2 * b + 1 + 3 = 2 * b + 4 by omega, show 2 * (2 * b + 1) + 9 + 6 = 4 * b + 17 by omega]
        exact r_p2e b
    rw [if_neg h2]
    -- an overflow: m = r + 2z + 3
    show Reach (Pc (a + 3) m) (overflow (a + 2 - (m - 3) / 2) ((m - 3) / 2) ((m - 3) % 2)).cfg
    have hm : m = (m - 3) % 2 + 2 * ((m - 3) / 2) + 3 := by omega
    have ho := r_over (a + 1) ((m - 3) / 2) ((m - 3) % 2) (by omega)
    rw [← hm, show a + 1 + 2 = a + 3 by omega, show a + 1 + 1 - (m - 3) / 2 = a + 2 - (m - 3) / 2 by omega] at ho
    exact reach_reaches ho (overflow_sem _ _ _ (Nat.mod_lt _ (by omega))).reaches

/-! ## Halting is the orbit question -/

/-- The orbit of `n` under `F`, `none` once it has hit a halting node. -/
def orbitFrom (n : Node) : Nat → Option Node
  | 0 => some n
  | k + 1 => (F n).bind (fun n' => orbitFrom n' k)

theorem runs_long (N : Nat) : ∀ n : Node, (∀ k, orbitFrom n k ≠ none) →
    ∃ m, N ≤ m ∧ ∃ c, steps m n.cfg = some c := by
  induction N with
  | zero => intro n _; exact ⟨0, Nat.le_refl 0, _, rfl⟩
  | succ N ih =>
    intro n hs
    cases hF : F n with
    | none => exact absurd (by simp [orbitFrom, hF]) (hs 1)
    | some n' =>
      have hs' : ∀ k, orbitFrom n' k ≠ none := fun k h => hs (k + 1) (by simp [orbitFrom, hF, h])
      obtain ⟨m, hm, c, hc⟩ := ih n' hs'
      have hr := F_sem n
      rw [hF] at hr
      obtain ⟨k, hk⟩ := hr
      exact ⟨k + 1 + m, by omega, c, steps_seq trans hk hc⟩

/-- **The machine halts from the node `n` iff the orbit of `n` under `F` reaches `none`.** -/
theorem halts_from (n : Node) : Halts trans n.cfg ↔ ∃ k, orbitFrom n k = none := by
  constructor
  · intro hh
    refine Classical.byContradiction fun hne => ?_
    have hs : ∀ k, orbitFrom n k ≠ none := fun k h => hne ⟨k, h⟩
    refine not_halts_of_forall trans ?_ hh
    exact forall_of_unbounded trans (fun m => ∃ c, steps m n.cfg = some c) (runs_long · n hs) (fun _ h => h)
  · rintro ⟨k, hk⟩
    induction k generalizing n with
    | zero => simp [orbitFrom] at hk
    | succ k ih =>
      have hr := F_sem n
      cases hF : F n with
      | none => rw [hF] at hr; exact hr
      | some n' =>
        rw [hF] at hr
        have hk' : orbitFrom n' k = none := by simpa [orbitFrom, hF] using hk
        exact halts_pre hr.reaches (ih n' hk')

/-- **Main theorem.** The machine halts from blank tape iff the orbit of `s 7` (the reset configuration `S 13`,
reached after 110 steps) under `F` reaches `none`. -/
theorem halts_iff : HaltsFromBlank ↔ ∃ k, orbitFrom (.s 7) k = none := by
  rw [← halts_from]
  constructor
  · intro hh
    refine Classical.byContradiction fun hne => ?_
    have hs : ∀ k, orbitFrom (.s 7) k ≠ none := fun k h => hne ((halts_from _).2 ⟨k, h⟩)
    refine not_halts_of_forall trans ?_ hh
    refine forall_of_unbounded trans (fun m => ∃ c, steps m init = some c) (fun N => ?_) (fun _ h => h)
    obtain ⟨m, hm, c, hc⟩ := runs_long N (.s 7) hs
    exact ⟨110 + m, by omega, c, steps_seq trans blank_to_S13 hc⟩
  · exact halts_pre ⟨110, blank_to_S13⟩

/-! ## The halting nodes -/

/-- The only nodes where `F` stops: a doubling round that starts with no ones, `p a 0`. -/
def InH : Node → Prop
  | .p _ m => m = 0
  | _ => False

theorem F_none_iff (n : Node) : F n = none ↔ InH n := by
  cases n with
  | s x => simp [F, InH]
  | t u v => simp [F, InH]
  | q u c =>
    simp only [F, InH, iff_false]
    split <;> (try split) <;> (try split) <;> (try split) <;> simp
  | p a m =>
    simp only [F, InH]
    by_cases hd : 2 * a + 9 ≤ m
    · rw [if_pos hd]; simp; omega
    rw [if_neg hd]
    by_cases h0 : m = 0
    · simp [h0]
    rw [if_neg h0]
    simp only [h0, iff_false]
    split <;> (try split) <;> (try split) <;> simp

theorem orbit_succ (k : Nat) : ∀ n : Node, orbitFrom n (k + 1) = (orbitFrom n k).bind F := by
  induction k with
  | zero => intro n; simp [orbitFrom]
  | succ k ih =>
    intro n
    show (F n).bind (fun n' => orbitFrom n' (k + 1)) = ((F n).bind (fun n' => orbitFrom n' k)).bind F
    cases F n with
    | none => rfl
    | some n' => exact ih n'

theorem orbit_none_iff (n : Node) :
    (∃ k, orbitFrom n k = none) ↔ ∃ k n', orbitFrom n k = some n' ∧ InH n' := by
  constructor
  · rintro ⟨k, hk⟩
    induction k with
    | zero => simp [orbitFrom] at hk
    | succ k ih =>
      rw [orbit_succ] at hk
      cases ho : orbitFrom n k with
      | none => exact ih ho
      | some n' =>
        rw [ho] at hk
        exact ⟨k, n', ho, (F_none_iff n').1 hk⟩
  · rintro ⟨k, n', hk, hH⟩
    exact ⟨k + 1, by rw [orbit_succ, hk]; exact (F_none_iff n').2 hH⟩

/-- **The machine halts from blank tape iff the orbit of `s 7` (= `S 13`) under `F` reaches a node `p a 0`**:
a doubling round `0^inf F> 0 0 (10)^(a+3) 0 1 0^inf` that finds no ones at all. -/
theorem halts_iff_H : HaltsFromBlank ↔ ∃ k a, orbitFrom (.s 7) k = some (.p a 0) := by
  rw [halts_iff, orbit_none_iff]
  constructor
  · rintro ⟨k, n', hk, hH⟩
    cases n' with
    | p a m => simp only [InH] at hH; subst hH; exact ⟨k, a, hk⟩
    | _ => exact absurd hH (by simp [InH])
  · rintro ⟨k, a, hk⟩
    exact ⟨k, .p a 0, hk, rfl⟩

/-! ## The orbit, evaluated

Once a node is `none` the orbit stays `none`, so one evaluation of `orbitFrom (.s 7) N` covers all the nodes before
it. 100,000 nodes are about 3,900 returns (up to `S 407,853`); 10^7 nodes about 299,000 returns (`S 34,793,745`). -/

theorem orbit_none_succ {n : Node} {k : Nat} (h : orbitFrom n k = none) : orbitFrom n (k + 1) = none := by
  rw [orbit_succ, h]; rfl

theorem orbit_some_of_le {n : Node} {k N : Nat} (hk : k ≤ N) (h : orbitFrom n N ≠ none) : orbitFrom n k ≠ none := by
  intro h0
  apply h
  obtain ⟨d, rfl⟩ : ∃ d, N = k + d := ⟨N - k, by omega⟩
  clear hk h
  induction d with
  | zero => exact h0
  | succ d ih => exact orbit_none_succ ih

set_option maxRecDepth 100000 in
/-- The first 100,000 nodes of the orbit of `S 13` do not halt (Lean's kernel). -/
theorem orbit_kernel : ∀ k ≤ 100000, orbitFrom (.s 7) k ≠ none :=
  fun _ hk => orbit_some_of_le hk (by decide +kernel)

/-- The first 10^7 nodes of the orbit of `S 13` do not halt (compiled evaluation). -/
theorem orbit_native : ∀ k ≤ 10000000, orbitFrom (.s 7) k ≠ none :=
  fun _ hk => orbit_some_of_le hk (by native_decide)

end H90097
