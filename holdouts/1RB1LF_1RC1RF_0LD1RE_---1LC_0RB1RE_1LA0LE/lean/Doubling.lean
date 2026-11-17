import Map

/-!
# 1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE halts iff a doubling map with a growing modulus reaches a halting pool

`Map.lean` proves that the machine halts iff the orbit of the visit `T(none, 2, 0)` under the node map `F` reaches
`none`.  This file proves, by arithmetic alone, that `F` is the map `op` of the explainer, on two kinds of states:

* `ev c u v` (an even pool; the bracket `c` is not touched):

      2u < v     u ← 2u,      v ← v + 1
      2u > v     u ← 2u − v,  v stays
      2u = v     the odd pool `od c (2v − 3) 0`

* `od c A b` (the visit `T(c, A, b)` with an odd pool `A = 2i + 3`; one operation is one whole sweep):

      b < i                 od c (A − 2b − 2) (2b + 2)               the pair block doubles
      b = i, no bracket     od none 1 (2b + 2)                       the halting visit
      b = i, bracket c      ev none (c + 2b + 5) (c + 2b + 7)        the bracket joins the pool
      b = i + r, r ≥ 1:
        no bracket          r = 1: od none (2A + 5) 0;  r = 2: ev none (A + 3) (A + 5);
                            r ≥ 3: ev (some (A + 1)) (r − 2) r      (the swept part stays behind as a bracket)
        bracket c           r = 1: od none (2c + 2A + 5) 0;  r ≥ 2: ev none (r − 1) (c + i + b + 6)   (merge)

  and `od none 1 b` is the halt.

A visit `T(c, a, b)` with `a` even is the state `ev c (b + 2) (a/2 + b + 3)` (`phi`), with `a` odd it is `od c a b`;
inside an even sweep, `Cs c (2i + 2) (2j + 1) w` (and `Cs c (2i + 2) (2j) 0`) is `ev c (j + w + 2) (i + 2j + w + 4)`:
a round does not move it, a carry is one operation, and the end of a sweep is the doubling.

Main results:
* `halts_iff_op`: **the machine halts from blank tape iff `op`, started at `ev none 2 4` (the visit `T(none, 2, 0)`,
  step 7), reaches the halt**;
* `halts_iff_pool`: **it halts iff the orbit of `op` reaches an odd pool without bracket `od none A 0` with
  `A = 2^(k+2) − 2k − 3`** for some `k` (1, 3, 9, 23, 53, 115, …);
* `pool_sources` and `event_pool`: such a pool comes from an event `2u = v` without bracket, and then it halts iff
  `v = 2^(k+1) − k`, or from one of the two rarer odd pools `2A + 5` (an odd pool that overflows by one) and
  `2c + 2A + 5` (a merge that ends as the tail runs out);
* `halts_iff_source`: **it halts iff the orbit meets an event `2u = v` without bracket at `v = 2^(k+1) − k`, or a
  merge `O_c(2i + 3, i + 1)` with `2c + 4i + 11 = 2^(k+2) − 2k − 3`**; the overflow pool `2A + 5` is always
  `2^(j+3) − 1` and never halts (`not_pool_mersenne`);
* `op_kernel`, `op_native`: the first 10^4 (kernel) and 10^7 (compiled) operations do not halt.

Nothing about the run is assumed beyond `Map.lean`; the axioms are `propext`, `Classical.choice`, `Quot.sound`.
-/

set_option linter.deprecated false

namespace H21883

/-! ## The map -/

inductive DS where
  | ev (c : Option Nat) (u v : Nat)
  | od (c : Option Nat) (A b : Nat)
  deriving DecidableEq, Repr

/-- One sweep of an odd pool `A = 2i + 3`. -/
def odStep (c : Option Nat) (i b : Nat) : Option DS :=
  if b < i then some (.od c (2 * (i - b) + 1) (2 * b + 2))
  else if b = i then
    match c with
    | none => some (.od none 1 (2 * b + 2))
    | some c => some (.ev none (c + 2 * b + 5) (c + 2 * b + 7))
  else
    match c with
    | none =>
      if b = i + 1 then some (.od none (4 * i + 11) 0)
      else if b = i + 2 then some (.ev none (2 * i + 6) (2 * i + 8))
      else some (.ev (some (2 * i + 4)) (b - i - 2) (b - i))
    | some c =>
      if b = i + 1 then some (.od none (2 * c + 4 * i + 11) 0)
      else some (.ev none (b - i - 1) (c + i + b + 6))

/-- One operation; `none` is the halt.  (States that no run meets map to themselves.) -/
def op : DS → Option DS
  | .ev c u v =>
    if 2 * u < v then some (.ev c (2 * u) (v + 1))
    else if v < 2 * u then some (.ev c (2 * u - v) v)
    else some (.od c (2 * v - 3) 0)
  | .od c A b =>
    if A = 1 ∧ c = none then none
    else if A % 2 = 1 ∧ 3 ≤ A then odStep c ((A - 3) / 2) b
    else some (.od c A b)

def opIter : Nat → DS → Option DS
  | 0, s => some s
  | n + 1, s => (op s).bind (opIter n)

theorem opIter_add (a b : Nat) (s : DS) : opIter (a + b) s = (opIter a s).bind (opIter b) := by
  induction a generalizing s with
  | zero => simp [opIter]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [opIter]
    cases op s with
    | none => rfl
    | some s' => exact ih s'

theorem opIter_one (s : DS) : opIter 1 s = op s := by
  simp only [opIter]; cases op s <;> rfl

theorem opIter_succ' (n : Nat) (s : DS) : opIter (n + 1) s = (opIter n s).bind op := by
  rw [opIter_add]; cases opIter n s <;> simp [opIter_one]

theorem op_lt (c : Option Nat) (u v : Nat) (h : 2 * u < v) : op (.ev c u v) = some (.ev c (2 * u) (v + 1)) := by
  simp [op, h]
theorem op_gt (c : Option Nat) (u v : Nat) (h : v < 2 * u) : op (.ev c u v) = some (.ev c (2 * u - v) v) := by
  simp [op, h, show ¬ 2 * u < v by omega]
theorem op_eq (c : Option Nat) (u v : Nat) (h : 2 * u = v) : op (.ev c u v) = some (.od c (2 * v - 3) 0) := by
  simp [op, show ¬ 2 * u < v by omega, show ¬ v < 2 * u by omega]
theorem op_od (c : Option Nat) (i b : Nat) : op (.od c (2 * i + 3) b) = odStep c i b := by
  simp only [op]
  rw [if_neg (show ¬ (2 * i + 3 = 1 ∧ c = none) by omega), if_pos (show (2 * i + 3) % 2 = 1 ∧ 3 ≤ 2 * i + 3 by omega), show (2 * i + 3 - 3) / 2 = i by omega]

theorem op_od' {c : Option Nat} {A i b : Nat} (h : A = 2 * i + 3) : op (.od c A b) = odStep c i b := by
  subst h; exact op_od c i b

/-! ## States of the machine as states of `op` -/

def phi : Node → DS
  | .vis c a b => if a % 2 = 0 then .ev c (b + 2) (a / 2 + b + 3) else .od c a b
  | .rs n => .ev none (n + 4) (n + 6)

/-- What `F` (or `inner`) says, in terms of `op`: at least one operation to the next node. -/
def OpSem (s : DS) : Option Node → Prop
  | some v => ∃ n, opIter (n + 1) s = some (phi v)
  | none => ∃ n, opIter n s = none

/-- The same, allowing no operation. -/
def OpSem0 (s : DS) : Option Node → Prop
  | some v => ∃ n, opIter n s = some (phi v)
  | none => ∃ n, opIter n s = none

theorem opsem_one {s t : DS} {o : Option Node} (h : op s = some t) (ht : OpSem0 t o) : OpSem s o := by
  cases o with
  | none =>
    obtain ⟨n, hn⟩ := ht
    exact ⟨1 + n, by rw [opIter_add, opIter_one, h]; exact hn⟩
  | some v =>
    obtain ⟨n, hn⟩ := ht
    exact ⟨n, by rw [show n + 1 = 1 + n by omega, opIter_add, opIter_one, h]; exact hn⟩

theorem opsem0_of {s : DS} {o : Option Node} (h : OpSem s o) : OpSem0 s o := by
  cases o with
  | none => exact h
  | some v => obtain ⟨n, hn⟩ := h; exact ⟨n + 1, hn⟩

theorem opsem0_one {s t : DS} {o : Option Node} (h : op s = some t) (ht : OpSem0 t o) : OpSem0 s o :=
  opsem0_of (opsem_one h ht)

theorem opsem_vis1 {s : DS} {v : Node} (h : op s = some (phi v)) : OpSem s (some v) :=
  ⟨0, by rw [opIter_one]; exact h⟩

theorem phi_ev {c : Option Nat} {a b : Nat} (h : a % 2 = 0) : phi (.vis c a b) = .ev c (b + 2) (a / 2 + b + 3) := by
  simp [phi, h]
theorem phi_od {c : Option Nat} {a b : Nat} (h : a % 2 = 1) : phi (.vis c a b) = .od c a b := by
  simp [phi, h]

/-- Close goals `some (..) = some (..)` between explicit states. -/
macro "fin" : tactic => `(tactic| first
  | rfl
  | (simp only [DS.ev.injEq, DS.od.injEq, Option.some.injEq, true_and, and_true]; omega))

/-! ## An even sweep is doubling operations -/

theorem inner_congr {c : Option Nat} {x n w x' n' w' : Nat} (hx : x = x') (hn : n = n') (hw : w = w') :
    inner c x n w = inner c x' n' w' := by subst hx; subst hn; subst hw; rfl

macro "icongr" : tactic => `(tactic| exact inner_congr (by omega) (by omega) (by omega))

/-- Unfold `inner` on both sides and close what is left. -/
macro "isimp" : tactic => `(tactic| (simp only [Nat.reduceAdd, Nat.reduceMul, Nat.mul_zero, Nat.zero_add, inner]
  <;> first | rfl | icongr | (congr 2 <;> omega) | (congr 3 <;> omega)))

/-- The state of `Cs c (2i + 2) (2j + 1) w` (`w ≥ 1`) and of `Cs c (2i + 2) (2j) 0`. -/
def evS (c : Option Nat) (i j w : Nat) : DS := .ev c (j + w + 2) (i + 2 * j + w + 4)

theorem ev_end (c : Option Nat) (i j : Nat) : OpSem (evS c i j 0) (inner c (2 * i + 2) (2 * j) 0) := by
  cases i with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, inner]
    apply opsem_vis1
    rw [phi_od (by omega), evS, op_eq _ _ _ (by omega)]; fin
  | succ i =>
    have : inner c (2 * (i + 1) + 2) (2 * j) 0 = some (.vis c (2 * i + 2) (2 * j + 2)) := by
      cases c with
      | none => rw [show 2 * (i + 1) + 2 = (2 * i + 1) + 3 by omega]; simp only [inner]; try icongr
      | some c => rw [show 2 * (i + 1) + 2 = (2 * i) + 4 by omega]; simp only [inner]; try icongr
    rw [this]; apply opsem_vis1
    rw [phi_ev (by omega), evS, op_lt _ _ _ (by omega)]; fin

theorem ev_sweep (w : Nat) : ∀ c i j, 1 ≤ w → OpSem (evS c i j w) (inner c (2 * i + 2) (2 * j + 1) w) := by
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro c i j hw
    match i, w with
    | i + 1, z + 3 =>
      have hi : inner c (2 * (i + 1) + 2) (2 * j + 1) (z + 3) = inner c (2 * i + 2) (2 * (j + 1) + 1) (z + 2) := by
        cases c with
        | none => rw [show 2 * (i + 1) + 2 = (2 * i + 1) + 3 by omega]; simp only [inner]; try icongr
        | some c => rw [show 2 * (i + 1) + 2 = (2 * i) + 4 by omega]; simp only [inner]; try icongr
      have e : evS c (i + 1) j (z + 3) = evS c i (j + 1) (z + 2) := by simp only [evS]; congr 1 <;> omega
      rw [hi, e]; exact ih (z + 2) (by omega) c i (j + 1) (by omega)
    | i + 1, 2 =>
      have hi : inner c (2 * (i + 1) + 2) (2 * j + 1) 2 = inner c (2 * i + 2) (2 * (j + 1) + 1) 1 := by
        cases c with
        | none => rw [show 2 * (i + 1) + 2 = (2 * i + 1) + 3 by omega]; simp only [inner]; try icongr
        | some c => rw [show 2 * (i + 1) + 2 = (2 * i) + 4 by omega]; simp only [inner]; try icongr
      have e : evS c (i + 1) j 2 = evS c i (j + 1) 1 := by simp only [evS]; congr 1 <;> omega
      rw [hi, e]; exact ih 1 (by omega) c i (j + 1) (by omega)
    | i + 1, 1 =>
      have hi : inner c (2 * (i + 1) + 2) (2 * j + 1) 1 = inner c (2 * i + 2) (2 * (j + 1)) 0 := by
        cases c with
        | none => rw [show 2 * (i + 1) + 2 = (2 * i + 1) + 3 by omega]; simp only [inner]; try icongr
        | some c => rw [show 2 * (i + 1) + 2 = (2 * i) + 4 by omega]; simp only [inner]; try icongr
      have e : evS c (i + 1) j 1 = evS c i (j + 1) 0 := by simp only [evS]; congr 1 <;> omega
      rw [hi, e]; exact ev_end c i (j + 1)
    | 0, z + 4 =>
      have hi : inner c (2 * 0 + 2) (2 * j + 1) (z + 4) = inner c (2 * (2 * j + 2) + 2) (2 * 0 + 1) (z + 2) := by
        simp only [Nat.mul_zero, Nat.zero_add, inner]; icongr
      rw [hi]
      refine opsem_one (t := evS c (2 * j + 2) 0 (z + 2)) ?_ (opsem0_of (ih (z + 2) (by omega) c _ 0 (by omega)))
      rw [evS, op_gt _ _ _ (by omega)]; simp only [evS]; fin
    | 0, 3 =>
      have hi : inner c (2 * 0 + 2) (2 * j + 1) 3 = inner c (2 * (2 * j + 2) + 2) (2 * 0 + 1) 1 := by
        simp only [Nat.mul_zero, Nat.zero_add, inner]; icongr
      rw [hi]
      refine opsem_one (t := evS c (2 * j + 2) 0 1) ?_ (opsem0_of (ih 1 (by omega) c _ 0 (by omega)))
      rw [evS, op_gt _ _ _ (by omega)]; simp only [evS]; fin
    | 0, 2 =>
      have hi : inner c (2 * 0 + 2) (2 * j + 1) 2 = inner c (2 * (2 * j + 2) + 2) (2 * 0) 0 := by
        simp only [Nat.mul_zero, Nat.zero_add, inner]; icongr
      rw [hi]
      refine opsem_one (t := evS c (2 * j + 2) 0 0) ?_ (opsem0_of (ev_end c _ 0))
      rw [evS, op_gt _ _ _ (by omega)]; simp only [evS]; fin
    | 0, 1 =>
      simp only [Nat.mul_zero, Nat.zero_add, inner]
      refine opsem_one (t := .ev c 1 (2 * j + 5)) ?_ (opsem0_of (opsem_vis1 ?_))
      · rw [evS, op_gt _ _ _ (by omega)]; fin
      · rw [phi_ev (by omega), op_lt _ _ _ (by omega)]; fin
    | _, 0 => omega

/-! ## An odd sweep is one operation -/

theorem odStep_lt {c : Option Nat} {i b : Nat} (h : b < i) :
    odStep c i b = some (.od c (2 * (i - b) + 1) (2 * b + 2)) := by
  unfold odStep; rw [if_pos h]
theorem odStep_eq_none {i b : Nat} (h : b = i) : odStep none i b = some (.od none 1 (2 * b + 2)) := by
  unfold odStep; rw [if_neg (by omega), if_pos h]
theorem odStep_eq_some {c i b : Nat} (h : b = i) :
    odStep (some c) i b = some (.ev none (c + 2 * b + 5) (c + 2 * b + 7)) := by
  unfold odStep; rw [if_neg (by omega), if_pos h]
theorem odStep_n1 {i b : Nat} (h : b = i + 1) : odStep none i b = some (.od none (4 * i + 11) 0) := by
  unfold odStep; rw [if_neg (by omega), if_neg (by omega)]; simp only; rw [if_pos h]
theorem odStep_n2 {i b : Nat} (h : b = i + 2) : odStep none i b = some (.ev none (2 * i + 6) (2 * i + 8)) := by
  unfold odStep; rw [if_neg (by omega), if_neg (by omega)]; simp only; rw [if_neg (by omega), if_pos h]
theorem odStep_n3 {i b : Nat} (h : i + 3 ≤ b) :
    odStep none i b = some (.ev (some (2 * i + 4)) (b - i - 2) (b - i)) := by
  unfold odStep; rw [if_neg (by omega), if_neg (by omega)]; simp only; rw [if_neg (by omega), if_neg (by omega)]
theorem odStep_s1 {c i b : Nat} (h : b = i + 1) : odStep (some c) i b = some (.od none (2 * c + 4 * i + 11) 0) := by
  unfold odStep; rw [if_neg (by omega), if_neg (by omega)]; simp only; rw [if_pos h]
theorem odStep_s2 {c i b : Nat} (h : i + 2 ≤ b) :
    odStep (some c) i b = some (.ev none (b - i - 1) (c + i + b + 6)) := by
  unfold odStep; rw [if_neg (by omega), if_neg (by omega)]; simp only; rw [if_neg (by omega)]

/-- The odd sweep from `T(c, 2i0 + 3, b0)`, at `Cs c (2i + 3) (2j + 1) w` with `i0 = i + j`, `b0 = w + j`. -/
theorem od_sweep (w : Nat) : ∀ c i j, 1 ≤ w →
    OpSem (.od c (2 * (i + j) + 3) (w + j)) (inner c (2 * i + 3) (2 * j + 1) w) := by
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro c i j hw
    have rnd : ∀ w', w' < w → 1 ≤ w' → ∀ i', i = i' + 1 → w' + (j + 1) = w + j →
        inner c (2 * i + 3) (2 * j + 1) w = inner c (2 * i' + 3) (2 * (j + 1) + 1) w' →
        OpSem (.od c (2 * (i + j) + 3) (w + j)) (inner c (2 * i + 3) (2 * j + 1) w) := by
      intro w' hw' h1 i' hi hb he
      rw [he, show 2 * (i + j) + 3 = 2 * (i' + (j + 1)) + 3 by omega, ← hb]
      exact ih w' hw' c i' (j + 1) h1
    cases c with
    | none =>
      match i, w with
      | i + 1, z + 3 =>
        exact rnd (z + 2) (by omega) (by omega) i rfl (by omega)
          (by rw [show 2 * (i + 1) + 3 = (2 * i + 2) + 3 by omega]; isimp)
      | i + 1, 2 =>
        exact rnd 1 (by omega) (by omega) i rfl (by omega)
          (by rw [show 2 * (i + 1) + 3 = (2 * i + 2) + 3 by omega]; isimp)
      | i + 1, 1 =>
        have : inner none (2 * (i + 1) + 3) (2 * j + 1) 1 = some (.vis none (2 * i + 1) (2 * j + 4)) := by
          rw [show 2 * (i + 1) + 3 = (2 * i + 2) + 3 by omega]; simp only [inner]
        rw [this]; apply opsem_vis1
        rw [phi_od (by omega), op_od]
        by_cases hi : i = 0
        · subst hi; rw [odStep_eq_none (by omega)]; fin
        · rw [odStep_lt (by omega)]; fin
      | 0, 1 =>
        have : inner none (2 * 0 + 3) (2 * j + 1) 1 = some (.vis none (4 * j + 11) 0) := by
          isimp
        rw [this]; apply opsem_vis1
        rw [phi_od (by omega), op_od, odStep_n1 (by omega)]; fin
      | 0, 2 =>
        have : inner none (2 * 0 + 3) (2 * j + 1) 2 = some (.rs (2 * j + 2)) := by
          isimp
        rw [this]; apply opsem_vis1
        rw [phi, op_od, odStep_n2 (by omega)]; fin
      | 0, z + 3 =>
        have hi : inner none (2 * 0 + 3) (2 * j + 1) (z + 3) = inner none 1 (2 * j + 3) (z + 2) := by
          simp only [Nat.mul_zero, Nat.zero_add]; simp only [inner]
        rw [hi, show 2 * (0 + j) + 3 = 2 * j + 3 by omega]
        refine opsem_one (by rw [op_od, odStep_n3 (by omega)]) (opsem0_of ?_)
        match z with
        | z + 3 =>
          have : inner none 1 (2 * j + 3) (z + 3 + 2) = inner (some (2 * j + 4)) (2 * 0 + 2) (2 * 0 + 1) (z + 2) := by
            isimp
          rw [this]
          have e : DS.ev (some (2 * j + 4)) (z + 3 + 3 + j - j - 2) (z + 3 + 3 + j - j) = evS (some (2 * j + 4)) 0 0 (z + 2) := by
            simp only [evS]; congr 1 <;> omega
          rw [e]; exact ev_sweep _ _ _ _ (by omega)
        | 2 =>
          have : inner none 1 (2 * j + 3) (2 + 2) = inner (some (2 * j + 4)) (2 * 0 + 2) (2 * 0 + 1) 1 := by
            isimp
          rw [this]
          have e : DS.ev (some (2 * j + 4)) (2 + 3 + j - j - 2) (2 + 3 + j - j) = evS (some (2 * j + 4)) 0 0 1 := by
            simp only [evS]; congr 1 <;> omega
          rw [e]; exact ev_sweep _ _ _ _ (by omega)
        | 1 =>
          have : inner none 1 (2 * j + 3) (1 + 2) = inner (some (2 * j + 4)) (2 * 0 + 2) (2 * 0) 0 := by
            isimp
          rw [this]
          have e : DS.ev (some (2 * j + 4)) (1 + 3 + j - j - 2) (1 + 3 + j - j) = evS (some (2 * j + 4)) 0 0 0 := by
            simp only [evS]; congr 1 <;> omega
          rw [e]; exact ev_end _ _ _
        | 0 =>
          have : inner none 1 (2 * j + 3) (0 + 2) = some (.vis (some (2 * j + 4)) 2 0) := by
            simp only [Nat.reduceAdd, inner]
          rw [this]
          apply opsem_vis1
          rw [phi_ev (by omega), op_lt _ _ _ (by omega)]; fin
      | _, 0 => omega
    | some c =>
      match i, w with
      | i + 1, z + 3 =>
        exact rnd (z + 2) (by omega) (by omega) i rfl (by omega)
          (by rw [show 2 * (i + 1) + 3 = (2 * i + 1) + 4 by omega]; isimp)
      | i + 1, 2 =>
        exact rnd 1 (by omega) (by omega) i rfl (by omega)
          (by rw [show 2 * (i + 1) + 3 = (2 * i + 1) + 4 by omega]; isimp)
      | i + 1, 1 =>
        rw [show 2 * (i + 1) + 3 = (2 * i + 1) + 4 by omega]; simp only [inner]
        cases i with
        | zero =>
          rw [show 2 * 0 + 1 + 2 = 3 from rfl]; simp only [inner]
          apply opsem_vis1
          rw [phi_ev (by omega), op_od, odStep_eq_some (by omega)]; fin
        | succ i =>
          rw [show 2 * (i + 1) + 1 + 2 = (2 * i + 1) + 4 by omega]; simp only [inner]
          apply opsem_vis1
          rw [phi_od (by omega), op_od, odStep_lt (by omega)]; fin
      | 0, 1 =>
        simp only [Nat.mul_zero, Nat.zero_add]; simp only [inner]
        apply opsem_vis1
        rw [phi_od (by omega), op_od, odStep_s1 (by omega)]; fin
      | 0, 2 =>
        simp only [Nat.mul_zero, Nat.zero_add]; simp only [inner]
        refine opsem_one (by rw [op_od, odStep_s2 (by omega)]) (opsem0_of (opsem_vis1 ?_))
        rw [phi_ev (by omega), op_lt _ _ _ (by omega)]; fin
      | 0, z + 3 =>
        simp only [Nat.mul_zero, Nat.zero_add]; simp only [inner]
        refine opsem_one (by rw [op_od, odStep_s2 (by omega)]) (opsem0_of ?_)
        match z with
        | z + 2 =>
          have : inner none 2 (c + (2 * j + 1) + 3) (z + 2 + 2) =
              inner none (2 * (c + 2 * j + 5) + 2) (2 * 0 + 1) (z + 2) := by
            rw [show c + (2 * j + 1) + 3 = c + 2 * j + 4 by omega]; try simp only [Nat.reduceAdd]
            conv => lhs; rw [inner]
            icongr
          rw [this]
          have e : DS.ev none (z + 2 + 3 + j - j - 1) (c + j + (z + 2 + 3 + j) + 6) = evS none (c + 2 * j + 5) 0 (z + 2) := by
            simp only [evS]; congr 1 <;> omega
          rw [e]; exact ev_sweep _ _ _ _ (by omega)
        | 1 =>
          have : inner none 2 (c + (2 * j + 1) + 3) (1 + 2) =
              inner none (2 * (c + 2 * j + 5) + 2) (2 * 0 + 1) 1 := by
            rw [show c + (2 * j + 1) + 3 = c + 2 * j + 4 by omega]; try simp only [Nat.reduceAdd]
            conv => lhs; rw [inner]
            icongr
          rw [this]
          have e : DS.ev none (1 + 3 + j - j - 1) (c + j + (1 + 3 + j) + 6) = evS none (c + 2 * j + 5) 0 1 := by
            simp only [evS]; congr 1 <;> omega
          rw [e]; exact ev_sweep _ _ _ _ (by omega)
        | 0 =>
          have : inner none 2 (c + (2 * j + 1) + 3) (0 + 2) =
              inner none (2 * (c + 2 * j + 5) + 2) (2 * 0) 0 := by
            rw [show c + (2 * j + 1) + 3 = c + 2 * j + 4 by omega]; try simp only [Nat.reduceAdd]
            conv => lhs; rw [inner]
            icongr
          rw [this]
          have e : DS.ev none (0 + 3 + j - j - 1) (c + j + (0 + 3 + j) + 6) = evS none (c + 2 * j + 5) 0 0 := by
            simp only [evS]; congr 1 <;> omega
          rw [e]; exact ev_end _ _ _
      | _, 0 => omega

/-! ## `F` is `op` -/

/-- **`F` is the map `op`**: from a node the run reaches, one or more operations lead to the next node, and `F`
halts iff `op` does. -/
theorem F_op (v : Node) (hg : Good v) : OpSem (phi v) (F v) := by
  match v with
  | .rs n =>
    have h := ev_sweep (n + 2) none 0 0 (by omega)
    rw [show evS none 0 0 (n + 2) = .ev none (n + 4) (n + 6) by simp only [evS]; congr 1 <;> omega] at h
    exact h
  | .vis c a b =>
    rcases Nat.lt_or_ge a 2 with ha | ha
    · simp only [Good] at hg
      rcases hg with h | ⟨rfl, rfl⟩
      · omega
      exact ⟨1, by simp [phi, opIter, op]⟩
    rcases Nat.mod_two_eq_zero_or_one a with hp | hp
    · obtain ⟨i, rfl⟩ : ∃ i, a = 2 * i + 2 := ⟨(a - 2) / 2, by omega⟩
      rw [phi_ev hp]
      match b with
      | z + 2 =>
        show OpSem _ (inner c (2 * i + 2) 1 (z + 2))
        have e : DS.ev c (z + 2 + 2) ((2 * i + 2) / 2 + (z + 2) + 3) = evS c i 0 (z + 2) := by
          simp only [evS]; congr 1 <;> omega
        rw [e]; exact ev_sweep _ _ _ _ (by omega)
      | 1 =>
        show OpSem _ (inner c (2 * i + 2) 1 1)
        have e : DS.ev c (1 + 2) ((2 * i + 2) / 2 + 1 + 3) = evS c i 0 1 := by
          simp only [evS]; congr 1 <;> omega
        rw [e]; exact ev_sweep _ _ _ _ (by omega)
      | 0 =>
        show OpSem _ (inner c (2 * i + 2) (2 * 0) 0)
        have e : DS.ev c (0 + 2) ((2 * i + 2) / 2 + 0 + 3) = evS c i 0 0 := by
          simp only [evS]; congr 1 <;> omega
        rw [e]; exact ev_end _ _ _
    · obtain ⟨i, rfl⟩ : ∃ i, a = 2 * i + 3 := ⟨(a - 3) / 2, by omega⟩
      rw [phi_od hp]
      match b with
      | z + 2 =>
        show OpSem _ (inner c (2 * i + 3) (2 * 0 + 1) (z + 2))
        have e : DS.od c (2 * i + 3) (z + 2) = DS.od c (2 * (i + 0) + 3) (z + 2 + 0) := rfl
        rw [e]; exact od_sweep _ _ _ _ (by omega)
      | 1 =>
        show OpSem _ (inner c (2 * i + 3) (2 * 0 + 1) 1)
        have e : DS.od c (2 * i + 3) 1 = DS.od c (2 * (i + 0) + 3) (1 + 0) := rfl
        rw [e]; exact od_sweep _ _ _ _ (by omega)
      | 0 =>
        show OpSem _ (inner c (2 * i + 3) 0 0)
        cases c with
        | none =>
          simp only [inner]
          apply opsem_vis1
          rw [phi_od (by omega), op_od]
          by_cases hi : i = 0
          · subst hi; rw [odStep_eq_none (by omega)]
          · rw [odStep_lt (by omega)]; fin
        | some c =>
          cases i with
          | zero =>
            simp only [Nat.mul_zero, Nat.zero_add, inner]
            apply opsem_vis1
            rw [phi_ev (by omega), op_od' (i := 0) rfl, odStep_eq_some (by omega)]; fin
          | succ i =>
            rw [show 2 * (i + 1) + 3 = (2 * i + 1) + 4 by omega]; simp only [inner]
            apply opsem_vis1
            rw [phi_od (by omega), op_od' (i := i + 1) (by omega), odStep_lt (by omega)]; fin

theorem opIter_some_prefix {a b : Nat} {s t : DS} (h : opIter (a + b) s = some t) : opIter a s ≠ none := by
  intro h0; rw [opIter_add, h0] at h; cases h

theorem orbit_op (v : Node) (hg : Good v) : (∃ k, orbit v k = none) ↔ ∃ n, opIter n (phi v) = none := by
  constructor
  · rintro ⟨k, hk⟩
    induction k generalizing v with
    | zero => simp [orbit] at hk
    | succ k ih =>
      have hr := F_op v hg
      have hs := F_sem v hg
      cases hF : F v with
      | none => rw [hF] at hr; exact hr
      | some v' =>
        rw [hF] at hr hs
        obtain ⟨j, hj⟩ := hr
        have hk' : orbit v' k = none := by simpa [orbit, hF] using hk
        obtain ⟨n, hn⟩ := ih v' hs.2 hk'
        exact ⟨j + 1 + n, by rw [opIter_add, hj]; exact hn⟩
  · rintro ⟨n, hn⟩
    refine Classical.byContradiction fun hne => ?_
    have key : ∀ n, ∀ v, Good v → (∀ k, orbit v k ≠ none) → opIter n (phi v) ≠ none := by
      intro n
      induction n using Nat.strongRecOn with
      | ind n ih =>
        intro v hg hs
        have hr := F_op v hg
        have hsem := F_sem v hg
        cases hF : F v with
        | none => exact absurd (by simp [orbit, hF]) (hs 1)
        | some v' =>
          rw [hF] at hr hsem
          obtain ⟨j, hj⟩ := hr
          have hs' : ∀ k, orbit v' k ≠ none := fun k h => hs (k + 1) (by simp [orbit, hF, h])
          by_cases hle : n ≤ j + 1
          · obtain ⟨d, hd⟩ : ∃ d, j + 1 = n + d := ⟨j + 1 - n, by omega⟩
            rw [hd] at hj
            exact opIter_some_prefix hj
          · obtain ⟨d, rfl⟩ : ∃ d, n = j + 1 + d := ⟨n - (j + 1), by omega⟩
            rw [opIter_add, hj]
            exact ih d (by omega) v' hsem.2 hs'
    exact key n v hg (fun k h => hne ⟨k, h⟩) hn

/-- The start: the visit `T(none, 2, 0)` (step 7) is `ev none 2 4`. -/
def s0 : DS := .ev none 2 4

/-- **Main theorem.** The machine halts from blank tape iff `op`, started at `ev none 2 4`, reaches the halt. -/
theorem halts_iff_op : HaltsFromBlank ↔ ∃ n, opIter n s0 = none := by
  rw [halts_iff, orbit_op _ (by simp [Good])]; rfl

/-! ## Halting pools -/

theorem op_ev_some (c : Option Nat) (u v : Nat) : op (.ev c u v) ≠ none := by
  simp only [op]; repeat' split
  all_goals simp

theorem odStep_some (c : Option Nat) (i b : Nat) : odStep c i b ≠ none := by
  unfold odStep; repeat' split
  all_goals simp

/-- `op` halts exactly at the visits `T(none, 1, b)`. -/
theorem op_none_iff (s : DS) : op s = none ↔ ∃ b, s = .od none 1 b := by
  constructor
  · intro h
    cases s with
    | ev c u v => exact absurd h (op_ev_some c u v)
    | od c A b =>
      simp only [op] at h
      split at h
      · next hc => obtain ⟨rfl, rfl⟩ := hc; exact ⟨b, rfl⟩
      · split at h
        · exact absurd h (odStep_some _ _ _)
        · cases h
  · rintro ⟨b, rfl⟩; simp [op]

/-- Where an odd pool without bracket comes from. -/
theorem op_to_od_none {s : DS} {B b : Nat} (h : op s = some (.od none B b)) (hB : B % 2 = 1) :
    b = 0 ∨ ∃ b', s = .od none (B + 2 * b' + 2) b' ∧ b = 2 * b' + 2 := by
  cases s with
  | ev c u v =>
    simp only [op] at h
    split at h
    · cases h
    · split at h
      · cases h
      · simp only [Option.some.injEq, DS.od.injEq] at h; exact Or.inl h.2.2.symm
  | od c A b0 =>
    simp only [op] at h
    split at h
    · cases h
    split at h
    · next hA =>
      obtain ⟨i, rfl⟩ : ∃ i, A = 2 * i + 3 := ⟨(A - 3) / 2, by omega⟩
      rw [show (2 * i + 3 - 3) / 2 = i by omega] at h
      unfold odStep at h
      split at h
      · simp only [Option.some.injEq, DS.od.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact Or.inr ⟨b0, by congr 1; omega, rfl⟩
      split at h
      · cases c with
        | none =>
          simp only [Option.some.injEq, DS.od.injEq] at h
          obtain ⟨-, rfl, rfl⟩ := h
          exact Or.inr ⟨b0, by congr 1; omega, rfl⟩
        | some c => simp at h
      · cases c with
        | none =>
          simp only at h
          split at h
          · simp only [Option.some.injEq, DS.od.injEq] at h; exact Or.inl h.2.2.symm
          split at h
          · simp at h
          · simp at h
        | some c =>
          simp only at h
          split at h
          · simp only [Option.some.injEq, DS.od.injEq] at h; exact Or.inl h.2.2.symm
          · simp at h
    · next h1 h2 =>
      simp only [Option.some.injEq, DS.od.injEq] at h
      obtain ⟨hc, hAB, -⟩ := h
      subst hc
      exfalso
      by_cases hB1 : A = 1
      · exact h1 ⟨hB1, rfl⟩
      · exact h2 ⟨by omega, by omega⟩

theorem two_pow_ge (k : Nat) : k + 2 ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

/-- An odd pool without bracket `A = B + 2^(k+2) − 2k − 4` doubles its pair block `k` times and is `B`. -/
theorem pool_run (k : Nat) : ∀ B, B % 2 = 1 →
    opIter k (.od none (B + 2 * 2 ^ (k + 1) - 2 * k - 4) 0) = some (.od none B (2 ^ (k + 1) - 2)) := by
  induction k with
  | zero => intro B _; simp [opIter]
  | succ k ih =>
    intro B hB
    have hP := two_pow_ge k
    rw [opIter_succ']
    have e : B + 2 * 2 ^ (k + 1 + 1) - 2 * (k + 1) - 4 = (B + 2 * 2 ^ (k + 1) - 2) + 2 * 2 ^ (k + 1) - 2 * k - 4 := by
      rw [Nat.pow_succ 2 (k + 1)]; omega
    rw [e, ih _ (by omega), Option.bind_some, Nat.pow_succ 2 (k + 1)]
    generalize 2 ^ (k + 1) = P at hP ⊢
    rw [op_od' (i := (B + 2 * P - 5) / 2) (by omega)]
    by_cases h1 : B = 1
    · subst h1; rw [odStep_eq_none (by omega)]; fin
    · rw [odStep_lt (by omega)]; fin

/-- The pools that halt: `A = 2^(k+2) − 2k − 3`. -/
def haltPool (k : Nat) : Nat := 2 * 2 ^ (k + 1) - 2 * k - 3

theorem haltPool_eq (k : Nat) : haltPool k = 2 ^ (k + 2) - 2 * k - 3 := by
  simp only [haltPool, Nat.pow_succ]; omega

/-- Backwards from an odd pool without bracket to the pool `T(none, A, 0)` it started as. -/
theorem back (n : Nat) : ∀ B b, opIter n s0 = some (.od none B b) → B % 2 = 1 →
    ∃ v k, opIter v s0 = some (.od none (B + 2 * 2 ^ (k + 1) - 2 * k - 4) 0) ∧ b = 2 ^ (k + 1) - 2 := by
  induction n with
  | zero => intro B b h; simp [opIter, s0] at h
  | succ n ih =>
    intro B b h hB
    rw [opIter_succ'] at h
    cases hs : opIter n s0 with
    | none => rw [hs] at h; cases h
    | some s =>
      rw [hs, Option.bind_some] at h
      rcases op_to_od_none h hB with rfl | ⟨b', rfl, rfl⟩
      · exact ⟨n + 1, 0, by rw [opIter_succ', hs, Option.bind_some, h]; congr 3, rfl⟩
      · obtain ⟨v, k, hm, hb⟩ := ih _ _ hs (by omega)
        have hP := two_pow_ge k
        refine ⟨v, k + 1, ?_, ?_⟩
        · rw [hm, hb, Nat.pow_succ 2 (k + 1)]; congr 3; omega
        · rw [hb, Nat.pow_succ 2 (k + 1)]; omega

/-- **The machine halts from blank tape iff the orbit of `op` reaches an odd pool without bracket
`T(none, A, 0)` with `A = 2^(k+2) − 2k − 3`** (1, 3, 9, 23, 53, 115, 241, …) for some `k`. -/
theorem halts_iff_pool : HaltsFromBlank ↔ ∃ n k, opIter n s0 = some (.od none (2 ^ (k + 2) - 2 * k - 3) 0) := by
  rw [halts_iff_op]
  constructor
  · rintro ⟨N, hN⟩
    induction N with
    | zero => simp [opIter] at hN
    | succ N ih =>
      rw [opIter_succ'] at hN
      cases hs : opIter N s0 with
      | none => exact ih hs
      | some s =>
        rw [hs, Option.bind_some] at hN
        obtain ⟨b, rfl⟩ := (op_none_iff s).1 hN
        obtain ⟨v, k, hm, -⟩ := back N 1 b hs rfl
        have hP := two_pow_ge k
        refine ⟨v, k, ?_⟩
        rw [hm, show 1 + 2 * 2 ^ (k + 1) - 2 * k - 4 = 2 ^ (k + 2) - 2 * k - 3 by simp only [Nat.pow_succ] at hP ⊢; omega]
  · rintro ⟨n, k, hn⟩
    have hP := two_pow_ge k
    refine ⟨n + k + 1, ?_⟩
    have hr := pool_run k 1 rfl
    rw [show 1 + 2 * 2 ^ (k + 1) - 2 * k - 4 = 2 ^ (k + 2) - 2 * k - 3 by simp only [Nat.pow_succ] at hP ⊢; omega] at hr
    rw [opIter_add, opIter_add, hn, Option.bind_some, hr, Option.bind_some, opIter_one]
    simp [op]

/-- Where a pool without bracket `T(none, A, 0)` comes from: an event `2u = v` without bracket (then `A = 2v − 3`,
so `A` is a halting pool iff `v = 2^(k+1) − k`), an odd pool that overflows by one (`A = 2A' + 5`), or a merge that
ends as the tail runs out (`A = 2c + 2A' + 5`). -/
theorem pool_sources {s : DS} {A : Nat} (h : op s = some (.od none A 0)) (hA : A % 2 = 1) :
    (∃ u v, s = .ev none u v ∧ 2 * u = v ∧ A = 2 * v - 3) ∨
    (∃ i, s = .od none (2 * i + 3) (i + 1) ∧ A = 2 * (2 * i + 3) + 5) ∨
    (∃ c i, s = .od (some c) (2 * i + 3) (i + 1) ∧ A = 2 * c + 2 * (2 * i + 3) + 5) := by
  cases s with
  | ev c u v =>
    simp only [op] at h
    split at h
    · cases h
    · split at h
      · cases h
      · simp only [Option.some.injEq, DS.od.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        exact Or.inl ⟨u, v, rfl, by omega, rfl⟩
  | od c A0 b0 =>
    simp only [op] at h
    split at h
    · cases h
    split at h
    · next hA0 =>
      obtain ⟨i, rfl⟩ : ∃ i, A0 = 2 * i + 3 := ⟨(A0 - 3) / 2, by omega⟩
      rw [show (2 * i + 3 - 3) / 2 = i by omega] at h
      unfold odStep at h
      split at h
      · simp only [Option.some.injEq, DS.od.injEq] at h; omega
      split at h
      · cases c with
        | none => simp only [Option.some.injEq, DS.od.injEq] at h; omega
        | some c => simp at h
      · cases c with
        | none =>
          simp only at h
          split at h
          · next hb =>
            simp only [Option.some.injEq, DS.od.injEq] at h
            subst hb; exact Or.inr (Or.inl ⟨i, rfl, by omega⟩)
          split at h
          · simp at h
          · simp at h
        | some c =>
          simp only at h
          split at h
          · next hb =>
            simp only [Option.some.injEq, DS.od.injEq] at h
            subst hb; exact Or.inr (Or.inr ⟨c, i, rfl, by omega⟩)
          · simp at h
    · next h1 h2 =>
      simp only [Option.some.injEq, DS.od.injEq] at h
      obtain ⟨hc, hAB, -⟩ := h
      subst hc
      exfalso
      by_cases hB1 : A0 = 1
      · exact h1 ⟨hB1, rfl⟩
      · exact h2 ⟨by omega, by omega⟩

theorem event_pool (k v : Nat) : 2 * v - 3 = 2 ^ (k + 2) - 2 * k - 3 ↔ v = 2 ^ (k + 1) - k := by
  have hP := two_pow_ge k
  rw [Nat.pow_succ 2 (k + 1)]; omega

/-! ## The pool 2A + 5 never halts -/

theorem pow3_ge (j : Nat) : 2 * j + 8 ≤ 2 ^ (j + 3) := by
  induction j with
  | zero => decide
  | succ j ih => rw [show j + 1 + 3 = (j + 3) + 1 by omega, Nat.pow_succ]; omega

theorem pow_ge_succ (d : Nat) : d + 2 ≤ 2 ^ (d + 1) := two_pow_ge d

/-- `2^(j+3) − 1` is never a halting pool `2^(k+2) − 2k − 3`. -/
theorem not_pool_mersenne (j k : Nat) : 2 ^ (j + 3) - 1 ≠ 2 ^ (k + 2) - 2 * k - 3 := by
  have hk := two_pow_ge (k + 1)
  have hj := pow3_ge j
  rw [show k + 1 + 1 = k + 2 from rfl] at hk
  rcases Nat.lt_or_ge (j + 3) (k + 2) with h | h
  · obtain ⟨d, rfl⟩ : ∃ d, k = j + 2 + d := ⟨k - (j + 2), by omega⟩
    rw [show j + 2 + d + 2 = (j + 3) + (d + 1) by omega, Nat.pow_add 2 (j + 3) (d + 1)]
    have hY := pow_ge_succ d
    have h1 : 2 ^ (j + 3) * (d + 2) ≤ 2 ^ (j + 3) * 2 ^ (d + 1) := Nat.mul_le_mul_left _ hY
    have h2 : 2 ^ (j + 3) * (d + 2) = 2 ^ (j + 3) * d + 2 ^ (j + 3) * 2 := Nat.mul_add _ _ _
    have h3 : 8 * d ≤ 2 ^ (j + 3) * d := Nat.mul_le_mul_right _ (by omega)
    clear hk
    generalize 2 ^ (j + 3) * 2 ^ (d + 1) = P at *
    generalize 2 ^ (j + 3) * (d + 2) = Q at *
    generalize 2 ^ (j + 3) * d = R at *
    omega
  · have := Nat.pow_le_pow_right (show 0 < 2 by decide) h
    omega

/-- **Halting, by its sources.** The machine halts from blank tape iff the orbit of `op` meets either an event
`2u = v` without bracket at a modulus `v = 2^(k+1) − k`, or a merge that ends as the tail runs out,
`O_c(2i + 3, i + 1)`, with `2c + 4i + 11 = 2^(k+2) − 2k − 3`.  The third source of odd pools without bracket, an odd
pool that overflows by one (`2A + 5`), is always `2^(j+3) − 1` and never halts. -/
theorem halts_iff_source : HaltsFromBlank ↔ ∃ n k,
    (∃ u, opIter n s0 = some (.ev none u (2 * u)) ∧ 2 * u = 2 ^ (k + 1) - k) ∨
    (∃ c i, opIter n s0 = some (.od (some c) (2 * i + 3) (i + 1)) ∧ 2 * c + 4 * i + 11 = 2 ^ (k + 2) - 2 * k - 3) := by
  rw [halts_iff_pool]
  constructor
  · rintro ⟨n, k, hn⟩
    have hP := two_pow_ge k
    have hodd : (2 ^ (k + 2) - 2 * k - 3) % 2 = 1 := by
      rw [Nat.pow_succ 2 (k + 1)]; omega
    cases n with
    | zero => simp [opIter, s0] at hn
    | succ n =>
      rw [opIter_succ'] at hn
      cases hs : opIter n s0 with
      | none => rw [hs] at hn; cases hn
      | some s =>
        rw [hs, Option.bind_some] at hn
        rcases pool_sources hn hodd with ⟨u, v, rfl, huv, hA⟩ | ⟨i, rfl, hA⟩ | ⟨c, i, rfl, hA⟩
        · subst huv
          exact ⟨n, k, Or.inl ⟨u, hs, (event_pool k (2 * u)).1 hA.symm⟩⟩
        · exfalso
          obtain ⟨w, j, -, hb⟩ := back n _ _ hs (by omega)
          have hj := two_pow_ge j
          apply not_pool_mersenne j k
          rw [hA, show j + 3 = (j + 1) + 1 + 1 by omega, Nat.pow_succ, Nat.pow_succ]
          omega
        · exact ⟨n, k, Or.inr ⟨c, i, hs, by omega⟩⟩
  · rintro ⟨n, k, ⟨u, hn, hu⟩ | ⟨c, i, hn, hc⟩⟩
    · refine ⟨n + 1, k, ?_⟩
      rw [opIter_succ', hn, Option.bind_some, op_eq _ _ _ rfl]
      have hP := two_pow_ge k
      congr 3; rw [hu, Nat.pow_succ 2 (k + 1)]; omega
    · refine ⟨n + 1, k, ?_⟩
      rw [opIter_succ', hn, Option.bind_some, op_od, odStep_s1 rfl, hc]

/-! ## The orbit, evaluated -/

theorem opIter_ne_of_le {k N : Nat} {s : DS} (hk : k ≤ N) (h : opIter N s ≠ none) : opIter k s ≠ none := by
  intro h0; apply h
  obtain ⟨d, rfl⟩ : ∃ d, N = k + d := ⟨N - k, by omega⟩
  rw [opIter_add, h0]; rfl

set_option maxRecDepth 100000 in
/-- The first 10,000 operations do not halt (Lean's kernel). -/
theorem op_kernel : ∀ k ≤ 10000, opIter k s0 ≠ none :=
  fun _ hk => opIter_ne_of_le hk (by decide +kernel)

/-- The first 10^7 operations do not halt (compiled evaluation). -/
theorem op_native : ∀ k ≤ 10000000, opIter k s0 ≠ none :=
  fun _ hk => opIter_ne_of_le hk (by native_decide)

end H21883
