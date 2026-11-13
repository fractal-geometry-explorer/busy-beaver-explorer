import Rules

/-!
# 1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB: the run is the orbit of a map on pairs of numbers

The rules of `Rules.lean`, put together.  With
  `fuel z = (10)^z 1 0^inf`,
  `D(k, y, z) = 0^inf (01)^(k+1) D> 1^(y+1) fuel z`,
  `A(m, z) = 0^inf A> 1^m fuel z`,
one round takes `D(k, 0, z)` to `D(k', 0, z')` with `(k', z') = next k z`, or halts when `next k z = none`
(`round`).  From blank tape the run reaches `D(0, 0, 5)` (`start`).  So the machine halts from blank tape exactly
when the orbit of `(0, 5)` under `next` reaches `none` (`halts_iff`).
-/

namespace H48709

open TM

/-- `(10)^z 1` then blank tape. -/
def fuel (z : Nat) : Tape := rep z [true, false] (cons true blank)
/-- `0^inf (01)^(k+1) D> 1^(y+1) (10)^z 1 0^inf`. -/
def Dc (k y z : Nat) : Config := ⟨rep (k + 1) [true, false] blank, rep (y + 1) [true] (fuel z), .D⟩
/-- `0^inf A> 1^m (10)^z 1 0^inf`. -/
def Ac (m z : Nat) : Config := ⟨blank, rep m [true] (fuel z), .A⟩

theorem cfb : cons false blank = blank := cons_false_blank

theorem rep_t_comm (n : Nat) (s : Tape) : rep n [true] (cons true s) = cons true (rep n [true] s) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

theorem rep_tf_comm (n : Nat) (s : Tape) :
    rep n [true, false] (cons true (cons false s)) = cons true (cons false (rep n [true, false] s)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

theorem rep_ft (n : Nat) (s : Tape) : rep n [false, true] (cons false s) = cons false (rep n [true, false] s) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

theorem rep_tt (n : Nat) (s : Tape) : rep n [true, true] s = rep (2 * n) [true] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    simp [ih]

/-- What follows the leading `1 0` of the fuel. -/
def fz : Nat → Tape
  | 0 => blank
  | z + 1 => fuel z

/-- The fuel tape starts with `1 0` (for `z = 0` the 0 is blank). -/
theorem fuel_split (z : Nat) : fuel z = cons true (cons false (fz z)) := by
  cases z with
  | zero => simp [fuel, fz, cfb]
  | succ z => simp [fuel, fz]

theorem some_cfg {a b : Config} (h : a = b) : some a = some b := by rw [h]

theorem ones_succ (y : Nat) (s : Tape) : rep (y + 1) [true] (cons true s) = rep (y + 2) [true] s := by
  rw [rep_t_comm]; rfl

theorem ones_add (a b : Nat) (s : Tape) : rep a [true] (rep b [true] s) = rep (a + b) [true] s :=
  (rep_add a b [true] s).symm

/-- `D(k+1, y, z) -> D(k, y+3, z)`. -/
theorem dstep (k y z : Nat) : steps (4 * k + 15) (Dc (k + 1) y z) = some (Dc k (y + 3) z) := by
  have h := d_step k y (fz z)
  have e : Dc (k + 1) y z = ⟨rep (k + 2) [true, false] blank, rep (y + 2) [true] (cons false (fz z)), .D⟩ := by
    simp only [Dc, fuel_split, ones_succ]
  rw [e, h]
  apply some_cfg
  have e2 : rep (y + 3 + 1) [true] (fuel z) = cons true (cons true (cons true (cons true (cons true (rep y [true] (cons false (fz z))))))) := by
    rw [fuel_split, ones_succ, show y + 3 + 2 = 5 + y by omega, ← ones_add]; rfl
  simp only [Dc, e2]
  rw [cfb, rep_ft]
  rfl

/-- `D(0, y, z) -> A(y+3, z)`. -/
theorem dzero (y z : Nat) : steps 8 (Dc 0 y z) = some (Ac (y + 3) z) := by
  have h := d_zero y (fz z)
  have e : Dc 0 y z = ⟨cons true (cons false blank), rep (y + 2) [true] (cons false (fz z)), .D⟩ := by
    simp only [Dc, fuel_split, ones_succ]; rfl
  rw [e, h]
  apply some_cfg
  have e2 : rep (y + 3) [true] (fuel z) = cons true (cons true (cons true (cons true (rep y [true] (cons false (fz z)))))) := by
    rw [fuel_split, show y + 3 = (y + 2) + 1 by omega, ones_succ, show y + 2 + 2 = 4 + y by omega, ← ones_add]; rfl
  simp only [Ac, e2, cfb]

/-- `D(k, y, z) -> A(y+3k+3, z)`, in some positive number of steps. -/
theorem drun (k : Nat) : ∀ y z, ∃ n, 0 < n ∧ steps n (Dc k y z) = some (Ac (y + 3 * k + 3) z) := by
  induction k with
  | zero => intro y z; exact ⟨8, by omega, by simpa using dzero y z⟩
  | succ k ih =>
    intro y z
    obtain ⟨n, hn, h⟩ := ih (y + 3) z
    refine ⟨4 * k + 15 + n, by omega, ?_⟩
    have e : y + 3 * (k + 1) + 3 = y + 3 + 3 * k + 3 := by omega
    rw [e]
    exact steps_seq trans (dstep k y z) h

theorem aodd (i z : Nat) : ∃ n, 0 < n ∧ steps n (Ac (2 * i + 1) (z + 1)) = some (Dc i 0 z) := by
  cases z with
  | zero =>
    refine ⟨2 * i + 4, by omega, ?_⟩
    have h := a_odd_one i
    rw [rep_tt] at h
    have e : Ac (2 * i + 1) (0 + 1) = ⟨blank, rep (2 * i) [true] (cons true (cons true (cons false (cons true blank)))), .A⟩ := by
      simp [Ac, fuel, rep_t_comm]
    rw [e, h]; apply some_cfg; simp [Dc, fuel]
  | succ z =>
    refine ⟨2 * i + 4, by omega, ?_⟩
    have h := a_odd i z
    rw [rep_tt] at h
    have e : Ac (2 * i + 1) (z + 1 + 1) = ⟨blank, rep (2 * i) [true] (cons true (rep (z + 2) [true, false] (cons true (blank)))), .A⟩ := by
      simp [Ac, fuel, rep_t_comm]
    rw [e, h]; apply some_cfg; simp [Dc, fuel]

theorem aeven (i z : Nat) : ∃ n, 0 < n ∧ steps n (Ac (2 * i + 2) (z + 2)) = some (Dc (i + 2) 0 z) := by
  cases z with
  | zero =>
    refine ⟨6 * i + 19, by omega, ?_⟩
    have h := a_even_two i
    rw [rep_tt] at h
    have e : Ac (2 * i + 2) (0 + 2) = ⟨blank, rep (2 * (i + 1)) [true] (cons true (cons false (cons true (cons false (cons true (blank)))))), .A⟩ := by
      rw [show 2 * (i + 1) = 2 * i + 2 by omega]; simp [Ac, fuel]
    rw [e, h]; apply some_cfg; rw [rep_tf_comm]; simp [Dc, fuel, cfb]
  | succ z =>
    refine ⟨6 * i + 19, by omega, ?_⟩
    have h := a_even i z
    rw [rep_tt] at h
    have e : Ac (2 * i + 2) (z + 1 + 2) = ⟨blank, rep (2 * (i + 1)) [true] (rep (z + 3) [true, false] (cons true (blank))), .A⟩ := by
      rw [show 2 * (i + 1) = 2 * i + 2 by omega, show z + 1 + 2 = z + 3 by omega]; simp [Ac, fuel]
    rw [e, h]; apply some_cfg; rw [rep_tf_comm]; simp [Dc, fuel, cfb]

theorem aodd_reset (i : Nat) : ∃ n, 0 < n ∧ steps n (Ac (2 * i + 1) 0) = some (Dc 0 0 (i + 1)) := by
  refine ⟨6 * i + 16, by omega, ?_⟩
  have h := reset_odd i
  rw [rep_tt] at h
  have e : Ac (2 * i + 1) 0 = ⟨blank, rep (2 * i) [true] (cons true (cons true (blank))), .A⟩ := by
    simp [Ac, fuel, rep_t_comm]
  rw [e, h]; apply some_cfg; simp [Dc, fuel, cfb, rep_ft]

theorem aeven_reset (i : Nat) : ∃ n, 0 < n ∧ steps n (Ac (2 * i + 2) 1) = some (Dc 0 0 (i + 3)) := by
  refine ⟨10 * i + 39, by omega, ?_⟩
  have h := reset_even i
  rw [rep_tt] at h
  have e : Ac (2 * i + 2) 1 = ⟨blank, rep (2 * (i + 1)) [true] (cons true (cons false (cons true (blank)))), .A⟩ := by
    rw [show 2 * (i + 1) = 2 * i + 2 by omega]; simp [Ac, fuel]
  rw [e, h]; apply some_cfg; simp [Dc, fuel, cfb, rep_ft]

theorem aeven_halt (i : Nat) : TM.Halts trans (Ac (2 * i + 2) 0) := by
  have h := halt_even i
  rw [rep_tt] at h
  have e : Ac (2 * i + 2) 0 = ⟨blank, rep (2 * (i + 1)) [true] (cons true (blank)), .A⟩ := by
    rw [show 2 * (i + 1) = 2 * i + 2 by omega]; simp [Ac, fuel]
  exact ⟨_, _, e ▸ h, rfl⟩

/-- One round of the map on `(k, z)`: `none` means the machine halts. -/
def next (k z : Nat) : Option (Nat × Nat) :=
  if k % 2 = 0 then
    (if z = 0 then some (0, 3 * (k / 2) + 2) else some (3 * (k / 2) + 1, z - 1))
  else
    (if z = 0 then none else if z = 1 then some (0, 3 * (k / 2) + 5) else some (3 * (k / 2) + 4, z - 2))

/-- One round: `D(k, 0, z)` reaches `D(k', 0, z')` when `next k z = some (k', z')`, and halts when it is `none`. -/
theorem round (k z : Nat) :
    (∀ k' z', next k z = some (k', z') → ∃ n, 0 < n ∧ steps n (Dc k 0 z) = some (Dc k' 0 z')) ∧
    (next k z = none → TM.Halts trans (Dc k 0 z)) := by
  obtain ⟨n₁, hn₁, h₁⟩ := drun k 0 z
  have hk := Nat.mod_two_eq_zero_or_one k
  rcases hk with hk | hk
  · -- k = 2j: A(6j+3, z) = A(2(3j+1)+1, z)
    have e : 0 + 3 * k + 3 = 2 * (3 * (k / 2) + 1) + 1 := by omega
    rw [e] at h₁
    refine ⟨fun k' z' hn => ?_, fun hn => ?_⟩
    · simp only [next, hk, ite_true] at hn
      by_cases hz : z = 0
      · simp only [hz, ite_true, Option.some.injEq, Prod.mk.injEq] at hn
        obtain ⟨rfl, rfl⟩ := hn
        subst hz
        obtain ⟨n₂, hn₂, h₂⟩ := aodd_reset (3 * (k / 2) + 1)
        exact ⟨n₁ + n₂, by omega, steps_seq trans h₁ (by simpa using h₂)⟩
      · simp only [hz, ite_false, Option.some.injEq, Prod.mk.injEq] at hn
        obtain ⟨rfl, rfl⟩ := hn
        obtain ⟨n₂, hn₂, h₂⟩ := aodd (3 * (k / 2) + 1) (z - 1)
        rw [show z - 1 + 1 = z by omega] at h₂
        exact ⟨n₁ + n₂, by omega, steps_seq trans h₁ h₂⟩
    · simp only [next, hk, ite_true] at hn
      split at hn <;> simp at hn
  · -- k = 2j+1: A(6j+6, z) = A(2(3j+2)+2, z)
    have e : 0 + 3 * k + 3 = 2 * (3 * (k / 2) + 2) + 2 := by omega
    rw [e] at h₁
    have hk' : ¬ (k % 2 = 0) := by omega
    refine ⟨fun k' z' hn => ?_, fun hn => ?_⟩
    · simp only [next, hk', ite_false] at hn
      by_cases hz : z = 0
      · simp [hz] at hn
      by_cases hz1 : z = 1
      · simp only [hz1, ite_true] at hn
        obtain ⟨rfl, rfl⟩ := hn
        subst hz1
        obtain ⟨n₂, hn₂, h₂⟩ := aeven_reset (3 * (k / 2) + 2)
        exact ⟨n₁ + n₂, by omega, steps_seq trans h₁ (by simpa [show 3 * (k / 2) + 2 + 3 = 3 * (k / 2) + 5 by omega] using h₂)⟩
      · simp only [hz, hz1, ite_false, Option.some.injEq, Prod.mk.injEq] at hn
        obtain ⟨rfl, rfl⟩ := hn
        obtain ⟨n₂, hn₂, h₂⟩ := aeven (3 * (k / 2) + 2) (z - 2)
        rw [show z - 2 + 2 = z by omega, show 3 * (k / 2) + 2 + 2 = 3 * (k / 2) + 4 by omega] at h₂
        exact ⟨n₁ + n₂, by omega, steps_seq trans h₁ h₂⟩
    · simp only [next, hk', ite_false] at hn
      by_cases hz : z = 0
      · subst hz
        obtain ⟨n₂, c, h₂, h₃⟩ := aeven_halt (3 * (k / 2) + 2)
        exact ⟨n₁ + n₂, c, steps_seq trans h₁ h₂, h₃⟩
      · by_cases hz1 : z = 1 <;> simp [hz, hz1] at hn

/-- From blank tape the run reaches `D(0, 0, 5)`. -/
theorem start' : steps 136 init = some (Dc 0 0 5) := by
  rw [show init = (⟨blank, blank, .A⟩ : Config) from rfl, start]
  apply some_cfg
  simp [Dc, fuel, cfb]

/-- The orbit of `(0, 5)` under `next`. -/
def orbit : Nat → Option (Nat × Nat)
  | 0 => some (0, 5)
  | i + 1 => match orbit i with
    | none => none
    | some (k, z) => next k z

theorem orbit_run (i : Nat) : ∀ k z, orbit i = some (k, z) → ∃ n, i ≤ n ∧ steps n init = some (Dc k 0 z) := by
  induction i with
  | zero =>
    intro k z h
    simp [orbit] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨136, by omega, start'⟩
  | succ i ih =>
    intro k z h
    simp only [orbit] at h
    cases ho : orbit i with
    | none => rw [ho] at h; cases h
    | some p =>
      obtain ⟨k₀, z₀⟩ := p
      rw [ho] at h
      obtain ⟨n, hn, hr⟩ := ih k₀ z₀ ho
      obtain ⟨m, hm, hr'⟩ := (round k₀ z₀).1 k z h
      exact ⟨n + m, by omega, steps_seq trans hr hr'⟩

/-- **The machine halts from blank tape exactly when the orbit of `(0, 5)` under `next` reaches `none`.** -/
theorem halts_iff : HaltsFromBlank ↔ ∃ i, orbit i = none := by
  constructor
  · intro hh
    apply Classical.byContradiction
    intro hno
    have hall : ∀ i, ∃ p, orbit i = some p := by
      intro i
      cases h : orbit i with
      | none => exact absurd ⟨i, h⟩ hno
      | some p => exact ⟨p, rfl⟩
    apply not_halts_of_forall trans _ hh
    apply forall_of_unbounded trans (fun n => ∃ c, steps n init = some c)
    · intro n
      obtain ⟨⟨k, z⟩, h⟩ := hall n
      obtain ⟨m, hm, hr⟩ := orbit_run n k z h
      exact ⟨m, hm, _, hr⟩
    · intro m hm; exact hm
  · intro ⟨i, hi⟩
    induction i with
    | zero => simp [orbit] at hi
    | succ i ih =>
      simp only [orbit] at hi
      cases ho : orbit i with
      | none => exact ih ho
      | some p =>
        obtain ⟨k, z⟩ := p
        rw [ho] at hi
        obtain ⟨n, -, hr⟩ := orbit_run i k z ho
        obtain ⟨m, c, h₁, h₂⟩ := (round k z).2 hi
        exact ⟨n + m, c, steps_seq trans hr h₁, h₂⟩

end H48709
