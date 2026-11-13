import Closed
import Exec

/-!
# Round-end classes of 1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA, checked by the executor

A class `c : Cls` is the set of round ends `node (c.r0 + c.m * x) c.tail`, x ≥ 0.  `clsRun T c` runs the executor
of `Exec.lean` from that node with x free and tests that it ends at `node (c.k + c.c * x) c.to`; `covers cs c`
tests that every `c.k + c.c * x` lies in a class of the list `cs` with tail `c.to`.  Both tests are proved sound
here, so a list of classes that passes them is closed under "next round end" (`closed_of_checks`).
-/

namespace H11019

open TM

/-- A word written as a string of 0s and 1s. -/
def bits (s : String) : List Bool := s.toList.map (· == '1')

/-- A round end as executor configuration: `A> 01001000 (01)^n T`. -/
def nodeS (n : Cnt) (T : List Bool) : SCfg :=
  ⟨[], [false, true, false, false, true, false, false, false].map .cell ++ (.blk [false, true] n :: T.map .cell), .A⟩

theorem dn_cells' (ρ : Nat → Nat) (w : List Bool) : dn ρ (w.map .cell) = app w blank := by
  have := dn_cells ρ w []
  rwa [List.append_nil] at this

theorem den_nodeS (ρ : Nat → Nat) (n : Cnt) (T : List Bool) : den ρ (nodeS n T) = node (n.eval ρ) T := by
  simp only [den, nodeS, dn_cells, dn, dn_cells']
  rfl

/-- The configuration is the round end `node n T` (compared in the form `canon`). -/
def atNode (S : SCfg) (n : Cnt) (T : List Bool) : Bool :=
  decide (S.l = [] ∧ S.st = .A ∧ canon S.r = canon (nodeS n T).r)

theorem atNode_spec {S : SCfg} {n : Cnt} {T : List Bool} (h : atNode S n T = true) (ρ : Nat → Nat) :
    den ρ S = node (n.eval ρ) T := by
  obtain ⟨l, r, st⟩ := S
  simp only [atNode, decide_eq_true_eq] at h
  obtain ⟨hl, hs, hc⟩ := h
  subst hl
  subst hs
  rw [← den_nodeS]
  have e : dn ρ r = dn ρ (nodeS n T).r := by rw [← canon_spec ρ r, hc, canon_spec]
  simp only [den, e]
  rfl

/-- A class of round ends and what one round does to it. -/
structure Cls where
  /-- the tail -/
  tail : List Bool
  /-- the big block has `r0 + m x` words -/
  r0 : Nat
  m : Nat
  /-- the round takes `K + 1` moves of the executor -/
  K : Nat
  /-- the next round end has tail `to` and `k + c x` words in the big block -/
  to : List Bool
  k : Nat
  c : Nat

/-- One round from the class, the count of the big block free: the executor ends at the announced round end. -/
def clsRun (T : Tbl) (c : Cls) : Bool :=
  (cross T.shR T.shL (nodeS ⟨c.r0, [c.m]⟩ c.tail)).isNone &&
  match run T (c.K + 1) (nodeS ⟨c.r0, [c.m]⟩ c.tail) with
  | some S => atNode S ⟨c.k, [c.c]⟩ c.to
  | none => false

theorem clsRun_sound {T : Tbl} (hT : T.OK) {c : Cls} (h : clsRun T c = true) (x : Nat) :
    ∃ n, 0 < n ∧ steps n (node (c.r0 + c.m * x) c.tail) = some (node (c.k + c.c * x) c.to) := by
  simp only [clsRun, Bool.and_eq_true] at h
  obtain ⟨hc, hr⟩ := h
  split at hr
  · rename_i S hS
    have hc' : cross T.shR T.shL (nodeS ⟨c.r0, [c.m]⟩ c.tail) = none := by
      cases hx : cross T.shR T.shL (nodeS ⟨c.r0, [c.m]⟩ c.tail) with
      | none => rfl
      | some v => rw [hx] at hc; cases hc
    obtain ⟨n, hn, hs⟩ := run_pos hT c.K hc' hS (fun _ => x)
    rw [den_nodeS, atNode_spec hr] at hs
    have e1 : Cnt.eval (fun _ => x) ⟨c.r0, [c.m]⟩ = c.r0 + c.m * x := by simp [Cnt.eval, dot]
    have e2 : Cnt.eval (fun _ => x) ⟨c.k, [c.c]⟩ = c.k + c.c * x := by simp [Cnt.eval, dot]
    rw [e1, e2] at hs
    exact ⟨n, hn, hs⟩
  · cases hr

/-- The round ends of a list of classes. -/
def InSet (cs : List Cls) (B : Nat) (T : List Bool) : Prop :=
  ∃ d ∈ cs, ∃ x, T = d.tail ∧ B = d.r0 + d.m * x

theorem exists_mul (a b m : Nat) (hle : b ≤ a) (h : a % m = b % m) : ∃ x, a = b + m * x := by
  have h0 := Nat.sub_mod_eq_zero_of_mod_eq h
  have := Nat.div_add_mod (a - b) m
  rw [h0] at this
  exact ⟨(a - b) / m, by omega⟩

/-- The classes with a given tail. -/
def cands (cs : List Cls) (T : List Bool) : List Cls := cs.filter (fun d => d.tail == T)

/-- A common multiple of their moduli. -/
def period (l : List Cls) : Nat := l.foldl (fun a d => Nat.lcm a d.m) 1

/-- `B` words with tail `T` is a round end of the list. -/
def inSetB (cs : List Cls) (B : Nat) (T : List Bool) : Bool :=
  (cands cs T).any (fun d => decide (d.r0 ≤ B) && B % d.m == d.r0 % d.m)

theorem inSetB_sound {cs : List Cls} {B : Nat} {T : List Bool} (h : inSetB cs B T = true) : InSet cs B T := by
  simp only [inSetB, cands, List.any_eq_true, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨d, ⟨hd, ht⟩, hle, hmod⟩ := h
  obtain ⟨x, hx⟩ := exists_mul B d.r0 d.m hle hmod
  exact ⟨d, hd, x, ht.symm, hx⟩

/-- Every `c.k + c.c * x` is in a class of `cs` with tail `c.to`: tested for x below a period `P`, each class used
having a modulus that divides `c.c * P`. -/
def covers (cs : List Cls) (c : Cls) : Bool :=
  let l := cands cs c.to
  let P := period l
  decide (0 < P) && (List.range P).all (fun j =>
    l.any (fun d => decide (d.r0 ≤ c.k + c.c * j) && (c.k + c.c * j) % d.m == d.r0 % d.m &&
      (c.c * P) % d.m == 0))

theorem covers_sound {cs : List Cls} {c : Cls} (h : covers cs c = true) (x : Nat) :
    InSet cs (c.k + c.c * x) c.to := by
  simp only [covers] at h
  generalize period (cands cs c.to) = P at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, List.any_eq_true, cands,
    List.mem_filter, beq_iff_eq] at h
  obtain ⟨hP, hall⟩ := h
  obtain ⟨d, ⟨hd, ht⟩, ⟨hle, hmod⟩, hdiv⟩ := hall (x % P) (Nat.mod_lt _ hP)
  obtain ⟨e, he⟩ := Nat.dvd_of_mod_eq_zero hdiv
  have hx : c.c * x = c.c * (x % P) + d.m * (e * (x / P)) := by
    have h1 := Nat.div_add_mod x P
    have h2 : c.c * x = c.c * (P * (x / P) + x % P) := by rw [h1]
    rw [h2, Nat.mul_add, ← Nat.mul_assoc, he, Nat.mul_assoc]
    omega
  have hle' : d.r0 ≤ c.k + c.c * x := by rw [hx]; omega
  have hmod' : (c.k + c.c * x) % d.m = d.r0 % d.m := by
    rw [hx, ← Nat.add_assoc, Nat.add_mul_mod_self_left]
    exact hmod
  obtain ⟨y, hy⟩ := exists_mul _ d.r0 d.m hle' hmod'
  exact ⟨d, hd, y, ht.symm, hy⟩

/-- A list of classes that passes both tests is closed under "next round end". -/
theorem closed_of_checks {T : Tbl} (hT : T.OK) {cs : List Cls}
    (h : ∀ c ∈ cs, (clsRun T c && covers cs c) = true) :
    ∀ B Tl, InSet cs B Tl → ∃ n B' T', 0 < n ∧ InSet cs B' T' ∧ steps n (node B Tl) = some (node B' T') := by
  intro B Tl hin
  obtain ⟨d, hd, x, rfl, rfl⟩ := hin
  have := h d hd
  simp only [Bool.and_eq_true] at this
  obtain ⟨n, hn, hs⟩ := clsRun_sound hT this.1 x
  exact ⟨n, _, _, hn, covers_sound this.2 x, hs⟩

/-- The run from blank tape reaches a round end, in `K` moves of the executor. -/
def arrives (T : Tbl) (K B : Nat) (Tl : List Bool) : Bool :=
  match run T K ⟨[], [], .A⟩ with
  | some S => atNode S ⟨B, []⟩ Tl
  | none => false

theorem arrives_sound {T : Tbl} (hT : T.OK) {K B : Nat} {Tl : List Bool} (h : arrives T K B Tl = true) :
    ∃ n, steps n init = some (node B Tl) := by
  simp only [arrives] at h
  split at h
  · rename_i S hS
    obtain ⟨n, hn⟩ := run_sound hT K hS (fun _ => 0)
    rw [atNode_spec h] at hn
    have e : Cnt.eval (fun _ => 0) ⟨B, []⟩ = B := by simp [Cnt.eval, dot]
    rw [e] at hn
    exact ⟨n, hn⟩
  · cases h

end H11019
