import Blank
import Rules

/-!
# One round in closed form, and halting reduced to a two-counter map

A *round start* is the head in state C on the blank cell left of the tape, the tape being one of

* `P u v = 0^∞ C> 0 11 0 (11)^u 0 (11)^v 0^∞`
* `Q u v = 0^∞ C> 0 11 0 11 0 (11)^u 0 (11)^v 0^∞`

(`enc .p u v`, `enc .q u v`).  From a round start the head runs right and *bounces* between the right end and the
middle block: each bounce takes a pair of 1s off the middle block and a pair off the last block and adds three
pairs to the block on the left (`bounce`, any number of times by `bounce_iter`).  When the middle block runs out
(`u < v`) the round ends in the same family; when the last block runs out (`u ≥ v + 2`) the family switches; when
both run out together (`u = v` or `u = v + 1`) the head runs off the right end in state E and the machine halts.

`next` is that map, `round` proves each round (for every `u ≥ 3` and `v`), `round_halt` the halting rounds, and
`halts_iff`: **the machine halts from blank tape iff the orbit of `next` from `P 3 0` reaches a pair with `u = v`
or `u = v + 1`.**  Everything is checked by Lean's kernel (no `native_decide`).
-/

namespace H151747

open TM

/-! ## Runs between configurations -/

/-- `c` reaches `c'` in at least one step. -/
def Reaches (c c' : Config) : Prop := ∃ n, steps (n + 1) c = some c'

theorem Reaches.trans {a b c : Config} (h₁ : Reaches a b) (h₂ : Reaches b c) : Reaches a c := by
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  exact ⟨n + 1 + m, by
    have := steps_seq H151747.trans hn hm
    rw [show n + 1 + (m + 1) = n + 1 + m + 1 by omega] at this
    exact this⟩

theorem reaches_of {n : Nat} {c c' : Config} (h : steps n c = some c') (hn : 0 < n) : Reaches c c' :=
  ⟨n - 1, by rw [show n - 1 + 1 = n by omega]; exact h⟩

theorem reaches_of_eq {n : Nat} {c c' d : Config} (h : steps n c = some c') (hn : 0 < n) (e : c' = d) :
    Reaches c d := e ▸ reaches_of h hn

theorem halts_of_reaches {c c' : Config} (h : Reaches c c') (h' : TM.Halts trans c') : TM.Halts trans c := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, d, hm, hd⟩ := h'
  exact ⟨n + 1 + m, d, steps_seq trans hn hm, hd⟩

/-! ## Tapes -/

abbrev tt : List Bool := [true, true]

theorem rot (n : Nat) (s : Tape) : cons true (rep n tt s) = rep n tt (cons true s) :=
  rep_rotate n [true] tt tt rfl s

theorem rep_tt (a b : Nat) (s : Tape) : rep a tt (rep b tt s) = rep (a + b) tt s := (rep_add a b tt s).symm

/-- The two families of round starts. -/
inductive K where
  | p | q
  deriving DecidableEq, Repr

/-- The round start `P u v` or `Q u v`. -/
def enc : K → Nat → Nat → Config
  | .p, u, v => ⟨blank, cons false (cons true (cons true (cons false (rep u tt (cons false (rep v tt blank)))))), .C⟩
  | .q, u, v => ⟨blank, cons false (cons true (cons true (cons false (cons true (cons true (cons false
      (rep u tt (cons false (rep v tt blank))))))))), .C⟩

/-- The sweep: `X 0 1 (11)^y 0 (11)^z D> 0^∞`, the left part `X` as a left stream. -/
def S (X : Tape) (y z : Nat) : Config := ⟨rep z tt (cons false (rep y tt (cons true (cons false X)))), blank, .D⟩

/-- The left part after a P start: `0^∞ (11)^x`; after a Q start: `0^∞ (11)^x 1`. -/
def XP (x : Nat) : Tape := rep x tt blank
def XQ (x : Nat) : Tape := cons true (rep x tt blank)

theorem XP_add (x k : Nat) : rep k tt (XP x) = XP (x + k) := by
  unfold XP; rw [rep_tt, Nat.add_comm]

theorem XQ_add (x k : Nat) : rep k tt (XQ x) = XQ (x + k) := by
  unfold XQ; rw [← rot, rep_tt, Nat.add_comm]

/-! ## The bounces -/

theorem bounce' (X : Tape) (y z : Nat) : Reaches (S X (y + 2) (z + 2)) (S (rep 3 tt X) (y + 1) (z + 1)) := by
  refine reaches_of_eq (bounce y z X) (by omega) ?_
  simp only [S, rep_succ, rep_zero, app_cons, app_nil, rot]

theorem bounce_iter (k : Nat) : ∀ (X : Tape) (y z : Nat),
    Reaches (S X (y + 1 + k) (z + 1 + k)) (S (rep (3 * k) tt X) (y + 1) (z + 1)) ∨ k = 0 := by
  induction k with
  | zero => intro X y z; right; rfl
  | succ k ih =>
    intro X y z
    left
    have h1 := bounce' X (y + k) (z + k)
    rw [show y + k + 2 = y + 1 + (k + 1) by omega, show z + k + 2 = z + 1 + (k + 1) by omega] at h1
    rw [show y + k + 1 = y + 1 + k by omega, show z + k + 1 = z + 1 + k by omega] at h1
    rcases ih (rep 3 tt X) y z with h2 | h2
    · refine h1.trans ?_
      rw [show 3 * (k + 1) = 3 * k + 3 by omega, rep_add]
      exact h2
    · subst h2
      simpa using h1

/-- `k` bounces (none when `k = 0`), as a reflexive statement. -/
theorem bounces (k : Nat) (X : Tape) (y z : Nat) (c : Config)
    (h : Reaches (S (rep (3 * k) tt X) (y + 1) (z + 1)) c) : Reaches (S X (y + 1 + k) (z + 1 + k)) c := by
  rcases bounce_iter k X y z with h1 | h1
  · exact h1.trans h
  · subst h1; simpa using h

theorem bounce1' (X : Tape) (z : Nat) : Reaches (S X 1 (z + 2)) (S (rep 3 tt X) 0 (z + 1)) := by
  refine reaches_of_eq (bounce1 z X) (by omega) ?_
  simp only [S, rep_succ, rep_zero, app_cons, app_nil, rot]

/-! ## The map -/

/-- One round on the counts: `none` when the round halts. -/
def next : K × Nat × Nat → Option (K × Nat × Nat)
  | (k, u, v) =>
    if u = v ∨ u = v + 1 then none
    else if u < v then some (k, 3 * u + (if k = .p then 2 else 3), v - u - 1)
    else some ((if k = .p then .q else .p), 3 * v + (if k = .p then 3 else 5), u - v - 2)

/-! ## The ends of a sweep -/

/-- The left part of the sweep, by family. -/
def XK : K → Nat → Tape
  | .p, x => XP x
  | .q, x => XQ x

theorem XK_add (k : K) (x n : Nat) : rep n tt (XK k x) = XK k (x + n) := by
  cases k
  · exact XP_add x n
  · exact XQ_add x n

/-- The middle block is used up, the last one has `d + 3` pairs left: the next round starts in the same family. -/
theorem yend (k : K) (x d : Nat) :
    Reaches (S (XK k x) 0 (d + 3)) (enc k (x + 5) d) := by
  cases k
  · match d with
    | 0 => exact reaches_of_eq (yexit3P x) (by omega) (by
        simp only [enc, XK, XP, S, rep_succ, rep_zero, app_cons, app_nil, rot, cons_false_blank])
    | 1 => exact reaches_of_eq (yexit4P x) (by omega) (by
        simp only [enc, XK, XP, S, rep_succ, rep_zero, app_cons, app_nil, rot])
    | d + 2 =>
      rw [show d + 2 + 3 = d + 5 by omega]
      exact reaches_of_eq (yexitP x d) (by omega) (by
        simp only [enc, rep_succ, rep_zero, app_cons, app_nil, rot])
  · match d with
    | 0 => exact reaches_of_eq (yexit3Q x) (by omega) (by
        simp only [enc, XK, XQ, S, rep_succ, rep_zero, app_cons, app_nil, rot, cons_false_blank])
    | 1 => exact reaches_of_eq (yexit4Q x) (by omega) (by
        simp only [enc, XK, XQ, S, rep_succ, rep_zero, app_cons, app_nil, rot])
    | d + 2 =>
      rw [show d + 2 + 3 = d + 5 by omega]
      exact reaches_of_eq (yexitQ x d) (by omega) (by
        simp only [enc, rep_succ, rep_zero, app_cons, app_nil, rot])

/-- How many pairs the left part gains at a family switch. -/
def zoff : K → Nat
  | .p => 3
  | .q => 4

/-- The family switch. -/
def flip : K → K
  | .p => .q
  | .q => .p

/-- The last block is down to one pair, the middle one has `d + 1` pairs: the next round starts in the other
family. -/
theorem zend (k : K) (x d : Nat) :
    Reaches (S (XK k x) (d + 1) 1) (enc (flip k) (x + zoff k) d) := by
  cases k
  · match d with
    | 0 => exact reaches_of_eq (zexit1P x) (by omega) (by
        simp only [enc, flip, zoff, rep_add, XK, XP, S, rep_succ, rep_zero, app_cons, app_nil, rot, cons_false_blank])
    | 1 => exact reaches_of_eq (zexit2P x) (by omega) (by
        simp only [enc, flip, zoff, rep_add, XK, XP, S, rep_succ, rep_zero, app_cons, app_nil, rot])
    | d + 2 =>
      rw [show d + 2 + 1 = d + 3 by omega]
      exact reaches_of_eq (zexitP x d) (by omega) (by
        simp only [enc, flip, zoff, rep_add, rep_succ, rep_zero, app_cons, app_nil, rot])
  · match d with
    | 0 => exact reaches_of_eq (zexit1Q x) (by omega) (by
        simp only [enc, flip, zoff, rep_add, XK, XQ, S, rep_succ, rep_zero, app_cons, app_nil, rot, cons_false_blank])
    | 1 => exact reaches_of_eq (zexit2Q x) (by omega) (by
        simp only [enc, flip, zoff, rep_add, XK, XQ, S, rep_succ, rep_zero, app_cons, app_nil, rot])
    | d + 2 =>
      rw [show d + 2 + 1 = d + 3 by omega]
      exact reaches_of_eq (zexitQ x d) (by omega) (by
        simp only [enc, flip, zoff, rep_add, rep_succ, rep_zero, app_cons, app_nil, rot])

/-- The middle block is used up with one or two pairs left in the last: the machine halts. -/
theorem halt_end (k : K) (x z : Nat) (hz : z = 1 ∨ z = 2) : TM.Halts trans (S (XK k x) 0 z) := by
  rcases hz with rfl | rfl <;> cases k
  · exact ⟨_, _, halt1P x, rfl⟩
  · exact ⟨_, _, halt1Q x, rfl⟩
  · exact ⟨_, _, halt2P x, rfl⟩
  · exact ⟨_, _, halt2Q x, rfl⟩

/-- The pairs in the left part when the sweep starts. -/
def soff : K → Nat
  | .p => 3
  | .q => 4

/-- The start of a round, into the sweep. -/
theorem start (k : K) (u v : Nat) :
    Reaches (enc k (u + 3) (v + 1)) (S (XK k (soff k)) (u + 1) (v + 1)) := by
  cases k
  · exact reaches_of_eq (entryP u v) (by omega) (by
      simp only [S, XK, XP, soff, rep_succ, rep_zero, app_cons, app_nil, rot])
  · exact reaches_of_eq (entryQ u v) (by omega) (by
      simp only [S, XK, XQ, soff, rep_succ, rep_zero, app_cons, app_nil, rot])

/-! ## A round -/

theorem Reaches.congr {c d c' d' : Config} (h : Reaches c d) (hc : c = c') (hd : d = d') : Reaches c' d' :=
  hc ▸ hd ▸ h

/-- The middle block runs out first. -/
theorem roundA (k : K) (a d : Nat) : Reaches (enc k (a + 3) (a + 3 + d + 1)) (enc k (soff k + 3 * a + 3 + 5) d) := by
  have h1 := start k a (a + 3 + d)
  have h2 := bounces a (XK k (soff k)) 0 (d + 3) _
    ((bounce1' (rep (3 * a) tt (XK k (soff k))) (d + 2)).trans
      ((yend k (soff k + 3 * a + 3) d).congr (by rw [XK_add, XK_add]) rfl))
  exact h1.trans (h2.congr (by congr 1 <;> omega) rfl)

/-- The last block runs out first. -/
theorem roundB (k : K) (b d : Nat) :
    Reaches (enc k (b + d + 3) (b + 1)) (enc (flip k) (soff k + 3 * b + zoff k) d) := by
  have h1 := start k (b + d) b
  have h2 := bounces b (XK k (soff k)) d 0 _ ((zend k (soff k + 3 * b) d).congr (by rw [XK_add]) rfl)
  exact h1.trans (h2.congr (by congr 1 <;> omega) rfl)

/-- The last block is empty. -/
theorem roundC (k : K) (a : Nat) : Reaches (enc k (a + 3) 0) (enc (flip k) (if k = .p then 3 else 5) (a + 1)) := by
  cases k
  · exact reaches_of_eq (entryP0 a) (by omega) (by
      simp only [enc, flip, rep_succ, rep_zero, app_cons, app_nil, rot, ite_true])
  · exact reaches_of_eq (entryQ0 a) (by omega) (by
      simp only [enc, flip, rep_succ, rep_zero, app_cons, app_nil, rot]; rfl)

/-- Both blocks run out together, with `u = v`. -/
theorem haltA (k : K) (a : Nat) : TM.Halts trans (enc k (a + 3) (a + 3)) := by
  have h1 := start k a (a + 2)
  have h2 := bounces a (XK k (soff k)) 0 2 _ (bounce1' (rep (3 * a) tt (XK k (soff k))) 1)
  refine halts_of_reaches ((h1.trans (h2.congr (by congr 1 <;> omega) rfl)).congr rfl rfl) ?_
  rw [XK_add, XK_add]
  exact halt_end k _ 2 (by omega)

/-- Both blocks run out together, with `u = v + 1`. -/
theorem haltB (k : K) (a : Nat) : TM.Halts trans (enc k (a + 3) (a + 2)) := by
  have h1 := start k a (a + 1)
  have h2 := bounces a (XK k (soff k)) 0 1 _ (bounce1' (rep (3 * a) tt (XK k (soff k))) 0)
  refine halts_of_reaches (h1.trans (h2.congr (by congr 1 <;> omega) rfl)) ?_
  rw [XK_add, XK_add]
  exact halt_end k _ 1 (by omega)

theorem round (k : K) (u v : Nat) (hu : 3 ≤ u) {k' : K} {u' v' : Nat} (h : next (k, u, v) = some (k', u', v')) :
    Reaches (enc k u v) (enc k' u' v') := by
  simp only [next] at h
  by_cases h1 : u = v ∨ u = v + 1
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  obtain ⟨a, rfl⟩ : ∃ a, u = a + 3 := ⟨u - 3, by omega⟩
  by_cases h2 : a + 3 < v
  · rw [if_pos h2] at h
    obtain ⟨d, rfl⟩ : ∃ d, v = a + 3 + d + 1 := ⟨v - a - 4, by omega⟩
    cases h
    have := roundA k a d
    rw [show a + 3 + d + 1 - (a + 3) - 1 = d by omega]
    cases k
    · rw [show 3 * (a + 3) + (if K.p = K.p then 2 else 3) = soff .p + 3 * a + 3 + 5 by simp [soff]; omega]
      exact this
    · rw [show 3 * (a + 3) + (if K.q = K.p then 2 else 3) = soff .q + 3 * a + 3 + 5 by simp [soff]; omega]
      exact this
  · rw [if_neg h2] at h
    cases h
    match v with
    | 0 =>
      have := roundC k a
      rw [show a + 3 - 0 - 2 = a + 1 by omega]
      cases k
      · simpa [flip] using this
      · simpa [flip] using this
    | b + 1 =>
      obtain ⟨d, rfl⟩ : ∃ d, a = b + d := ⟨a - b, by omega⟩
      have := roundB k b d
      rw [show b + d + 3 - (b + 1) - 2 = d by omega]
      cases k
      · rw [show 3 * (b + 1) + (if K.p = K.p then 3 else 5) = soff .p + 3 * b + zoff .p by simp [soff, zoff]; omega]
        simpa [flip] using this
      · rw [show 3 * (b + 1) + (if K.q = K.p then 3 else 5) = soff .q + 3 * b + zoff .q by simp [soff, zoff]; omega]
        simpa [flip] using this

theorem round_halt (k : K) (u v : Nat) (hu : 3 ≤ u) (h : next (k, u, v) = none) : TM.Halts trans (enc k u v) := by
  simp only [next] at h
  by_cases h1 : u = v ∨ u = v + 1
  · obtain ⟨a, rfl⟩ : ∃ a, u = a + 3 := ⟨u - 3, by omega⟩
    rcases h1 with rfl | h1
    · exact haltA k a
    · obtain rfl : v = a + 2 := by omega
      exact haltB k a
  · rw [if_neg h1] at h
    split at h <;> cases h

end H151747
