import Orbit
import SpecialPhase

/-!
# The run of 1RB0RE_0LC1LE_0RD1LD_1RA1LF_1LC0RA_0LB--- from blank tape, phase by phase, as a theorem

A state is a word shape (`K2`: the level-1 counter C1, the counter C3 that moves by four, or S2t = `1 0^a 1 (001)^b`)
with the tape `app p blank` to its left, the counts a, b and the length z of the run of zeros.  `next2` is the first
of the proved rules that applies: the five rules of CounterPhase.lean (any p) and the cycle-end phases of
SpecialPhase.lean and Phase.lean (`phase_D0`), for the five short words p they need.  `next2_sound`: each step is a
run of the machine of at least z' steps.

From blank tape the first phase start is ⟨c1, [], 2, 0, 15⟩ (step 457).  `iter2_kernel`: Lean's kernel runs the map
for 100,000 phases (no halt in the first 10^17610 steps, `blank_kernel`).  `iter2_native`: compiled evaluation (`native_decide`) runs it
for 1,000,000 phases: z then has 176,093 digits, so no halt in the first 10^176092 steps (`blank_native`).  py/phaseiter.py runs the
same phases with the machine itself (no rules) and agrees.  Written by hand.
-/

namespace H53125

open TM

inductive K2 where
  | c1 | c3 | s2
  deriving DecidableEq, Repr

structure S where
  k : K2
  p : List Bool
  a : Nat
  b : Nat
  z : Nat
  deriving DecidableEq, Repr

def S.tape (x : S) : Tape :=
  match x.k with
  | .c1 => C1 (app x.p blank) x.a x.b
  | .c3 => C3 (app x.p blank) x.a x.b
  | .s2 => S2t (app x.p blank) x.a x.b

def cfg2 (x : S) : Config := PS x.tape x.z

def Good (x y : S) : Prop := ∃ s, y.z ≤ s ∧ steps s (cfg2 x) = some (cfg2 y)

/-! The phases, with z written as 4j + c. -/

theorem mk1 {W W' : Tape} {z z' : Nat} (hz : z % 4 = 1 ∧ 9 ≤ z)
    (hp : ∀ j, ∃ s, 6 * j + 15 ≤ s ∧ steps s (PS W (4 * j + 9)) = some (PS W' (6 * j + 15)))
    (e : z' = 3 * (z + 1) / 2) : ∃ s, z' ≤ s ∧ steps s (PS W z) = some (PS W' z') := by
  obtain ⟨s, hs, h⟩ := hp ((z - 9) / 4)
  rw [show 4 * ((z - 9) / 4) + 9 = z by omega, show 6 * ((z - 9) / 4) + 15 = z' by omega] at h
  exact ⟨s, by omega, h⟩

theorem mk3 {W W' : Tape} {z z' c : Nat} (hz : z % 4 = 3 ∧ 11 ≤ z)
    (hp : ∀ j, ∃ s, 6 * j + c ≤ s ∧ steps s (PS W (4 * j + 11)) = some (PS W' (6 * j + c)))
    (e : z' = 6 * ((z - 11) / 4) + c) : ∃ s, z' ≤ s ∧ steps s (PS W z) = some (PS W' z') := by
  obtain ⟨s, hs, h⟩ := hp ((z - 11) / 4)
  rw [show 4 * ((z - 11) / 4) + 11 = z by omega, ← e] at h
  exact ⟨s, by omega, h⟩

theorem mk2 {W W' : Tape} {z z' : Nat} (hz : z % 4 = 2 ∧ 10 ≤ z)
    (hp : ∀ j, ∃ s, 6 * j + 15 ≤ s ∧ steps s (PS W (4 * j + 10)) = some (PS W' (6 * j + 15)))
    (e : z' = 3 * z / 2) : ∃ s, z' ≤ s ∧ steps s (PS W z) = some (PS W' z') := by
  obtain ⟨s, hs, h⟩ := hp ((z - 10) / 4)
  rw [show 4 * ((z - 10) / 4) + 10 = z by omega, show 6 * ((z - 10) / 4) + 15 = z' by omega] at h
  exact ⟨s, by omega, h⟩

theorem mk0 {W W' : Tape} {z z' : Nat} (hz : z % 4 = 0 ∧ 8 ≤ z)
    (hp : ∀ j, ∃ s, 6 * j + 9 ≤ s ∧ steps s (PS W (4 * j + 8)) = some (PS W' (6 * j + 9)))
    (e : z' = 3 * z / 2 - 3) : ∃ s, z' ≤ s ∧ steps s (PS W z) = some (PS W' z') := by
  obtain ⟨s, hs, h⟩ := hp ((z - 8) / 4)
  rw [show 4 * ((z - 8) / 4) + 8 = z by omega, show 6 * ((z - 8) / 4) + 9 = z' by omega] at h
  exact ⟨s, by omega, h⟩

/-! The rules. -/

def p1000 : List Bool := [false, false, false, true]
def p10010 : List Bool := [false, true, false, false, true]
def p6 : List Bool := [false, false, true, false, false, false, false, false, false, true]
def p1001000 : List Bool := [false, false, false, true, false, false, true]
def p100100010 : List Bool := [false, true, false, false, false, true, false, false, true]

/-- Z ≡ 1: every word but `1 1` (S2t with a = b = 0) ends in `0 1` and stays. -/
def rKeep (x : S) : Option S :=
  if x.z % 4 = 1 ∧ 9 ≤ x.z ∧ ¬ (x.k = .s2 ∧ x.a = 0 ∧ x.b = 0) then some { x with z := 3 * (x.z + 1) / 2 } else none

/-- Keep `y` if z ≡ 3 mod 4 and z ≥ 11. -/
def if3 (z : Nat) (y : S) : Option S := if z % 4 = 3 ∧ 11 ≤ z then some y else none

def rTick (x : S) : Option S :=
  match x with
  | ⟨.c1, p, a + 1, b, z⟩ => if3 z ⟨.c1, p, a, b + 1, 3 * (z - 1) / 2⟩
  | ⟨.c3, p, a + 5, b, z⟩ => if3 z ⟨.c3, p, a + 1, b + 2, 3 * (z - 1) / 2⟩
  | _ => none

def rTwo (x : S) : Option S :=
  match x with
  | ⟨.s2, p, a + 1, 0, z⟩ => if z % 4 = 2 ∧ 10 ≤ z then some ⟨.c1, p, a, 0, 3 * z / 2⟩ else none
  | _ => none

def rZero (x : S) : Option S :=
  match x with
  | ⟨.s2, p, a + 8, 0, z⟩ => if z % 4 = 0 ∧ 8 ≤ z then some ⟨.c3, p, a + 4, 1, 3 * z / 2 - 3⟩ else none
  | _ => none

/-- The cycle ends met in the first 1,000,000 phases. -/
def rSpecial (x : S) : Option S :=
  match x with
  | ⟨.c1, [], 0, b, z⟩ => if3 z ⟨.s2, [], 3 * b + 5, 0, 3 * (z + 1) / 2⟩
  | ⟨.c3, [], 3, b, z⟩ => if3 z ⟨.s2, [], 6, b + 2, 3 * (z - 1) / 2⟩
  | ⟨.s2, [], 6, b + 1, z⟩ => if3 z ⟨.s2, p1000, 3 * b + 6, 0, 3 * (z + 1) / 2⟩
  | ⟨.c3, [false, false, false, true], 2, b + 1, z⟩ => if3 z ⟨.s2, p10010, 3 * b + 9, 0, 3 * (z + 1) / 2⟩
  | ⟨.c1, [false, true, false, false, true], 0, b + 1, z⟩ => if3 z ⟨.s2, [], 3 * b + 14, 0, 3 * (z + 1) / 2⟩
  | ⟨.c3, [], 1, b + 1, z⟩ => if3 z ⟨.s2, [], 3 * b + 9, 0, 3 * (z + 1) / 2⟩
  | ⟨.c3, [false, false, false, true], 4, b + 1, z⟩ => if3 z ⟨.s2, p6, 3 * b + 9, 0, 3 * (z + 1) / 2⟩
  | ⟨.c1, [false, false, true, false, false, false, false, false, false, true], 0, b, z⟩ =>
      if3 z ⟨.s2, p1001000, 4, b + 1, 3 * (z - 1) / 2⟩
  | ⟨.s2, [false, false, false, true, false, false, true], 4, b + 1, z⟩ =>
      if3 z ⟨.s2, p100100010, 3 * b + 6, 0, 3 * (z + 1) / 2⟩
  | _ => none

theorem if3_some {z : Nat} {y y' : S} (h : if3 z y = some y') : (z % 4 = 3 ∧ 11 ≤ z) ∧ y = y' := by
  unfold if3 at h
  split at h
  · cases h; exact ⟨‹_›, rfl⟩
  · cases h

theorem ends01 (x : S) (h : ¬ (x.k = .s2 ∧ x.a = 0 ∧ x.b = 0)) : ∃ X, x.tape = cons true (cons false X) := by
  obtain ⟨k, p, a, b, z⟩ := x
  cases k with
  | c1 => exact C1_ends _ a b
  | c3 => exact C3_ends _ a b
  | s2 =>
    cases b with
    | succ b => exact ⟨_, rfl⟩
    | zero =>
      cases a with
      | zero => exact absurd ⟨rfl, rfl, rfl⟩ h
      | succ a => exact ⟨_, rfl⟩

theorem rKeep_sound (x y : S) (h : rKeep x = some y) : Good x y := by
  unfold rKeep at h
  split at h
  · rename_i hc
    cases h
    obtain ⟨X, hX⟩ := ends01 x hc.2.2
    unfold Good cfg2
    show ∃ s, _ ≤ s ∧ steps s (PS x.tape x.z) = some (PS x.tape _)
    rw [hX]
    exact mk1 ⟨hc.1, hc.2.1⟩ (phase_keep X) rfl
  · cases h

theorem rTick_sound (x y : S) (h : rTick x = some y) : Good x y := by
  unfold rTick at h
  split at h
  · obtain ⟨hc, rfl⟩ := if3_some h; exact mk3 hc (phase_tick1 _ _ _) (by dsimp only at hc ⊢; omega)
  · obtain ⟨hc, rfl⟩ := if3_some h; exact mk3 hc (phase_tick3 _ _ _) (by dsimp only at hc ⊢; omega)
  · cases h

theorem rTwo_sound (x y : S) (h : rTwo x = some y) : Good x y := by
  unfold rTwo at h
  split at h
  · split at h
    · cases h; exact mk2 ‹_› (phase_rtwo _ _) rfl
    · cases h
  · cases h

theorem rZero_sound (x y : S) (h : rZero x = some y) : Good x y := by
  unfold rZero at h
  split at h
  · split at h
    · cases h; exact mk0 ‹_› (phase_rzero _ _) rfl
    · cases h
  · cases h

theorem rSpecial_sound (x y : S) (h : rSpecial x = some y) : Good x y := by
  unfold rSpecial at h
  split at h
  · obtain ⟨hc, rfl⟩ := if3_some h; exact mk3 hc (fun j => phase_D0 _ j) (by dsimp only at hc ⊢; omega)
  · obtain ⟨hc, rfl⟩ := if3_some h; exact mk3 hc (phase_sp2 _) (by dsimp only at hc ⊢; omega)
  · obtain ⟨hc, rfl⟩ := if3_some h; exact mk3 hc (phase_sp3 _) (by dsimp only at hc ⊢; omega)
  · obtain ⟨hc, rfl⟩ := if3_some h; exact mk3 hc (phase_sp4 _) (by dsimp only at hc ⊢; omega)
  · obtain ⟨hc, rfl⟩ := if3_some h; exact mk3 hc (phase_sp5 _) (by dsimp only at hc ⊢; omega)
  · obtain ⟨hc, rfl⟩ := if3_some h; exact mk3 hc (phase_sp6 _) (by dsimp only at hc ⊢; omega)
  · obtain ⟨hc, rfl⟩ := if3_some h; exact mk3 hc (phase_sp7 _) (by dsimp only at hc ⊢; omega)
  · obtain ⟨hc, rfl⟩ := if3_some h; exact mk3 hc (phase_sp8 _) (by dsimp only at hc ⊢; omega)
  · obtain ⟨hc, rfl⟩ := if3_some h; exact mk3 hc (phase_sp9 _) (by dsimp only at hc ⊢; omega)
  · cases h

/-- One phase: the first rule that applies. -/
def next2 (x : S) : Option S :=
  (rKeep x).orElse fun _ => (rTick x).orElse fun _ => (rTwo x).orElse fun _ =>
    (rZero x).orElse fun _ => rSpecial x

theorem next2_sound (x y : S) (h : next2 x = some y) : Good x y := by
  unfold next2 at h
  cases h1 : rKeep x with
  | some y' => rw [h1] at h; cases h; exact rKeep_sound x _ h1
  | none =>
    rw [h1] at h
    cases h2 : rTick x with
    | some y' => rw [h2] at h; cases h; exact rTick_sound x _ h2
    | none =>
      rw [h2] at h
      cases h3 : rTwo x with
      | some y' => rw [h3] at h; cases h; exact rTwo_sound x _ h3
      | none =>
        rw [h3] at h
        cases h4 : rZero x with
        | some y' => rw [h4] at h; cases h; exact rZero_sound x _ h4
        | none => rw [h4] at h; exact rSpecial_sound x y h

/-- n phases, tail-recursive. -/
def iter2 : Nat → S → Option S
  | 0, x => some x
  | n + 1, x => match next2 x with
    | some y => iter2 n y
    | none => none

theorem iter2_sound (n : Nat) (x y : S) (h : iter2 n x = some y) :
    ∃ s, y.z ≤ s + x.z ∧ steps s (cfg2 x) = some (cfg2 y) := by
  induction n generalizing x with
  | zero => cases h; exact ⟨0, by omega, rfl⟩
  | succ n ih =>
    unfold iter2 at h
    cases hx : next2 x with
    | none => rw [hx] at h; cases h
    | some x' =>
      rw [hx] at h
      obtain ⟨s1, hs1, h1⟩ := next2_sound x x' hx
      obtain ⟨s2, hs2, h2⟩ := ih x' h
      exact ⟨s1 + s2, by omega, steps_seq trans h1 h2⟩

def y0 : S := ⟨.c1, [], 2, 0, 15⟩

theorem blank_y0 : steps 457 init = some (cfg2 y0) := blank_x0

theorem bound_of {n e : Nat} (h : (iter2 n y0).any (fun y => decide (10 ^ e ≤ y.z)) = true) :
    ∃ s c, 10 ^ e ≤ s ∧ steps s init = some c := by
  cases hy : iter2 n y0 with
  | none => rw [hy] at h; cases h
  | some y =>
    rw [hy] at h
    simp only [Option.any_some, decide_eq_true_eq] at h
    obtain ⟨s, hs, h2⟩ := iter2_sound n y0 y hy
    exact ⟨457 + s, cfg2 y, by simp [y0] at hs; omega, steps_seq trans blank_y0 h2⟩

/-- Lean's kernel runs the proved phase map 100,000 phases from blank tape (exact integers, about 40 s). -/
theorem iter2_kernel : (iter2 100000 y0).any (fun y => decide (10 ^ 17610 ≤ y.z)) = true := by decide +kernel

/-- **No halt in the first 10^17610 steps from blank tape** (kernel). -/
theorem blank_kernel : ∃ s c, 10 ^ 17610 ≤ s ∧ steps s init = some c := bound_of iter2_kernel

/-- Compiled evaluation (`native_decide`) runs the map 1,000,000 phases: z has 176,093 digits. -/
theorem iter2_native : (iter2 1000000 y0).any (fun y => decide (10 ^ 176092 ≤ y.z)) = true := by native_decide

/-- **No halt in the first 10^176092 steps from blank tape** (the rules are kernel-checked theorems; the
evaluation of the map is compiled code). -/
theorem blank_native : ∃ s c, 10 ^ 176092 ≤ s ∧ steps s init = some c := bound_of iter2_native

end H53125
