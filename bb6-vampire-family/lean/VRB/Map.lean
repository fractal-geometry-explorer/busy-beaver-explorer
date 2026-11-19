import VRB.Rules
import TM.Fin

/-!
# The E-event map of the core with F0 = 1RB, and the run as its orbit

The E-pass (`ev`, `od`) halves the block into `(01)^q` with a short block left at the end, and the block then
drains (`Core.drain`): for every left tape `P`,

    P E> 1^n   reaches   Cq P q m,   m = 2u + 2 + 3q        (`pass`)

with q = n/2 - 1 + 0, u = 2 for n even and q = (n-3)/2 + 1, u = 2 for n odd.  Then the context rewrites the
block (`Core.tbl_sound`) according to b = q mod 2.  `nextE c n` is the next E-event after `Ev c n` by the table, and
`haltE c n` says that the table proves a halt from `Ev c n`; `nextE_sound`, `haltE_sound` hold for every n >= 6.
`check_sound`: if `check K x` finds a halting entry within K passes from an E-event that a start configuration
reaches, the run from that start halts.  `not_halts_of_forall`: if the orbit stays in the table forever, it never
halts.
-/

namespace VRB

open TM

abbrev Reaches := Core.Reaches f0

theorem pass_even (P : Tape) (k : Nat) :
    Reaches (Core.EvT P (2 * k + 2)) (Core.Cq P (k) (2 * 2 + 2 + 3 * (k))) (2 * k + 2) := by
  have h := ev k P
  rw [Core.tt_ones'] at h
  have h₁ : Reaches (Core.EvT P (2 * k + 2)) (Core.Cn (rep (k) [true, false] P) (2 * 2 + 2)) (2 * k + 2) :=
    ⟨_, by omega, h⟩
  have h₂ := Core.Reaches.trans' h₁ (Core.drain f0 P (k) 2)
  rw [Nat.add_zero] at h₂
  exact h₂

theorem pass_odd (P : Tape) (k : Nat) :
    Reaches (Core.EvT P (2 * k + 3)) (Core.Cq P (k + 1) (2 * 2 + 2 + 3 * (k + 1))) (2 * k + 3) := by
  have h := od k P
  rw [show cons true (rep (k + 1) [true, true] blank) = Core.ones (2 * k + 3) by
    rw [Core.tt_ones]; rw [show 2 * k + 3 = 2 * (k + 1) + 1 by omega]; rfl] at h
  have h₁ : Reaches (Core.EvT P (2 * k + 3)) (Core.Cn (rep (k + 1) [true, false] P) (2 * 2 + 2)) (2 * k + 3) :=
    ⟨_, by omega, h⟩
  have h₂ := Core.Reaches.trans' h₁ (Core.drain f0 P (k + 1) 2)
  rw [Nat.add_zero] at h₂
  exact h₂

/-- q of the pass. -/
def qOf (n : Nat) : Nat := if n % 2 = 0 then n / 2 - 1 + 0 else (n - 3) / 2 + 1

/-- The block length after the pass. -/
def mOf (n : Nat) : Nat := if n % 2 = 0 then 2 * 2 + 2 + 3 * qOf n else 2 * 2 + 2 + 3 * qOf n

theorem pass (P : Tape) (n : Nat) (h6 : 6 ≤ n) : Reaches (Core.EvT P n) (Core.Cq P (qOf n) (mOf n)) n := by
  by_cases hn : n % 2 = 0
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 2 := ⟨n / 2 - 1, by omega⟩
    have h := pass_even P k
    have e1 : qOf (2 * k + 2) = k := by simp only [qOf]; split <;> omega
    have e2 : mOf (2 * k + 2) = 2 * 2 + 2 + 3 * (k) := by
      simp only [mOf, e1]; split <;> omega
    rw [e1, e2]; exact h
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 3 := ⟨(n - 3) / 2, by omega⟩
    have h := pass_odd P k
    have e1 : qOf (2 * k + 3) = k + 1 := by simp only [qOf]; split <;> omega
    have e2 : mOf (2 * k + 3) = 2 * 2 + 2 + 3 * (k + 1) := by
      simp only [mOf, e1]; split <;> omega
    rw [e1, e2]; exact h

theorem mOf_even (n : Nat) (h : qOf n % 2 = 0) : ∃ j, mOf n = 2 * j + 2 :=
  ⟨mOf n / 2 - 1, by simp only [mOf] at *; split <;> omega⟩

theorem mOf_odd (n : Nat) (h : qOf n % 2 = 1) : ∃ j, mOf n = 2 * j + 5 :=
  ⟨(mOf n - 5) / 2, by simp only [mOf] at *; split <;> omega⟩

/-- The entry used by `Ev c n`: b = q mod 2. -/
def pick (x : Option (List Bool × Nat) × Option (List Bool × Nat)) (n : Nat) : Option (List Bool × Nat) :=
  if qOf n % 2 = 0 then x.1 else x.2

/-- The next E-event after `Ev c n` by the table, or `none` (a halting entry, a context outside the table, or
n < 6). -/
def nextE (c : List Bool) (n : Nat) : Option (List Bool × Nat) :=
  match Core.look c with
  | none => none
  | some x => if n < 6 then none else (pick x n).map (fun y => (y.1, mOf n + y.2))

/-- The table proves a halt from `Ev c n`. -/
def haltE (c : List Bool) (n : Nat) : Bool :=
  match Core.look c with
  | none => false
  | some x => !(n < 6) && (pick x n).isNone

theorem nextE_sound {c : List Bool} {n : Nat} {y : List Bool × Nat} (h : nextE c n = some y) :
    Reaches (Core.Ev c n) (Core.Ev y.1 y.2) n := by
  unfold nextE at h
  cases hl : Core.look c with
  | none => rw [hl] at h; cases h
  | some x =>
    rw [hl] at h
    obtain ⟨ok0, ok1⟩ := Core.look_sound f0 hl
    by_cases h6 : n < 6
    · simp only [h6, ↓reduceIte] at h; cases h
    simp only [h6, ↓reduceIte] at h
    have r := pass (app c.reverse blank) n (by omega)
    unfold pick at h
    by_cases hq : qOf n % 2 = 0
    · simp only [hq, ↓reduceIte] at h
      cases he : x.1 with
      | none => rw [he] at h; cases h
      | some p =>
        rw [he] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        simp only [he] at ok0
        obtain ⟨j, hj⟩ := mOf_even n hq
        have k := ok0 j
        simp only [Core.Cq, hq, ↓reduceIte] at r
        rw [hj] at r ⊢
        have r2 := Core.Reaches.trans' r k
        rw [Nat.add_zero] at r2
        exact r2
    · have hq1 : qOf n % 2 = 1 := by omega
      simp only [hq, ↓reduceIte] at h
      cases he : x.2 with
      | none => rw [he] at h; cases h
      | some p =>
        rw [he] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        simp only [he] at ok1
        obtain ⟨j, hj⟩ := mOf_odd n hq1
        have k := ok1 j
        simp only [Core.Cq, hq, ↓reduceIte] at r
        rw [hj] at r ⊢
        have r2 := Core.Reaches.trans' r k
        rw [Nat.add_zero] at r2
        exact r2

theorem haltE_sound {c : List Bool} {n : Nat} (h : haltE c n = true) : Halts trans (Core.Ev c n) := by
  unfold haltE at h
  cases hl : Core.look c with
  | none => rw [hl] at h; cases h
  | some x =>
    rw [hl] at h
    obtain ⟨ok0, ok1⟩ := Core.look_sound f0 hl
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Option.isNone_iff_eq_none] at h
    obtain ⟨h6, hp⟩ := h
    have r := pass (app c.reverse blank) n (by omega)
    unfold pick at hp
    by_cases hq : qOf n % 2 = 0
    · simp only [hq, ↓reduceIte] at hp
      simp only [hp] at ok0
      obtain ⟨j, hj⟩ := mOf_even n hq
      simp only [Core.Cq, hq, ↓reduceIte] at r
      rw [hj] at r
      exact Core.halts_of_reaches r (ok0 j)
    · have hq1 : qOf n % 2 = 1 := by omega
      simp only [hq, ↓reduceIte] at hp
      simp only [hp] at ok1
      obtain ⟨j, hj⟩ := mOf_odd n hq1
      simp only [Core.Cq, hq, ↓reduceIte] at r
      rw [hj] at r
      exact Core.halts_of_reaches r (ok1 j)

/-! ## The orbit -/

/-- `K` passes on (context, block, steps so far); `none` when the orbit leaves the table or halts. -/
def oiter : Nat → List Bool × Nat × Nat → Option (List Bool × Nat × Nat)
  | 0, x => some x
  | K + 1, x =>
    match nextE x.1 x.2.1 with
    | none => none
    | some y => oiter K (y.1, y.2, x.2.2 + x.2.1)

/-- Within `K` passes the orbit comes to an E-event at which the table proves a halt. -/
def check : Nat → List Bool × Nat × Nat → Bool
  | 0, x => haltE x.1 x.2.1
  | K + 1, x =>
    haltE x.1 x.2.1 ||
    match nextE x.1 x.2.1 with
    | none => false
    | some y => check K (y.1, y.2, x.2.2 + x.2.1)

theorem orbit_sound (c0 : Core.Config) : ∀ (K : Nat) (x y : List Bool × Nat × Nat), oiter K x = some y →
    Reaches c0 (Core.Ev x.1 x.2.1) x.2.2 → Reaches c0 (Core.Ev y.1 y.2.1) y.2.2 := by
  intro K
  induction K with
  | zero => intro x y h r; simp only [oiter, Option.some.injEq] at h; subst h; exact r
  | succ K ih =>
    intro x y h r
    simp only [oiter] at h
    cases hn : nextE x.1 x.2.1 with
    | none => rw [hn] at h; cases h
    | some z =>
      rw [hn] at h
      exact ih _ y h (Core.Reaches.trans' r (nextE_sound hn))

theorem check_sound (c0 : Core.Config) : ∀ (K : Nat) (x : List Bool × Nat × Nat), check K x = true →
    Reaches c0 (Core.Ev x.1 x.2.1) x.2.2 → Halts trans c0 := by
  intro K
  induction K with
  | zero => intro x h r; exact Core.halts_of_reaches r (haltE_sound h)
  | succ K ih =>
    intro x h r
    simp only [check, Bool.or_eq_true] at h
    rcases h with h | h
    · exact Core.halts_of_reaches r (haltE_sound h)
    · cases hn : nextE x.1 x.2.1 with
      | none => rw [hn] at h; cases h
      | some z =>
        rw [hn] at h
        exact ih _ h (Core.Reaches.trans' r (nextE_sound hn))

theorem nextE_ge {c : List Bool} {n : Nat} {y : List Bool × Nat} (h : nextE c n = some y) : 6 ≤ n := by
  unfold nextE at h
  cases hl : Core.look c with
  | none => rw [hl] at h; cases h
  | some x =>
    rw [hl] at h
    by_cases h6 : n < 6
    · simp only [h6, ↓reduceIte] at h; cases h
    · omega

theorem oiter_steps_ge : ∀ (K : Nat) (x y : List Bool × Nat × Nat), oiter K x = some y → x.2.2 + K ≤ y.2.2 := by
  intro K
  induction K with
  | zero => intro x y h; simp only [oiter, Option.some.injEq] at h; subst h; omega
  | succ K ih =>
    intro x y h
    simp only [oiter] at h
    cases hn : nextE x.1 x.2.1 with
    | none => rw [hn] at h; cases h
    | some z =>
      rw [hn] at h
      have := ih _ y h
      have := nextE_ge hn
      simp only at *
      omega

/-- No halt in the first `y.2.2` steps if the orbit gets to `y`. -/
theorem no_halt_of (c0 : Core.Config) (x : List Bool × Nat × Nat) (hx : Reaches c0 (Core.Ev x.1 x.2.1) x.2.2)
    (K : Nat) (y : List Bool × Nat × Nat) (h : oiter K x = some y) : ∃ c, steps y.2.2 c0 = some c := by
  obtain ⟨t, ht, s⟩ := orbit_sound c0 K x y h hx
  have s' : steps (y.2.2 + (t - y.2.2)) c0 = some (Core.Ev y.1 y.2.1) := by
    rw [show y.2.2 + (t - y.2.2) = t by omega]; exact s
  exact steps_le trans s'

/-- If the orbit stays inside the table forever, the run from `c0` never halts. -/
theorem not_halts_of_forall (c0 : Core.Config) (x : List Bool × Nat × Nat)
    (hx : Reaches c0 (Core.Ev x.1 x.2.1) x.2.2) (h : ∀ K, (oiter K x).isSome = true) : ¬ Halts trans c0 := by
  apply TM.not_halts_of_forall trans
  intro t
  have hK := h t
  cases e : oiter t x with
  | none => rw [e] at hK; cases hK
  | some y =>
    obtain ⟨u, hu, s⟩ := orbit_sound c0 t x y e hx
    have ge := oiter_steps_ge t x y e
    have s' : steps (t + (u - t)) c0 = some (Core.Ev y.1 y.2.1) := by
      rw [show t + (u - t) = u by omega]; exact s
    exact steps_le trans s'

/-! ## From blank tape -/

/-- Drop trailing `false`s. -/
def strip : List Bool → List Bool
  | [] => []
  | b :: l => if strip l = [] ∧ b = false then [] else b :: strip l

theorem app_strip (l : List Bool) : app (strip l) blank = app l blank := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    by_cases h : strip l = [] ∧ b = false
    · rw [strip, ite_eq_left_of_eq_true _ _ (eq_true h)]
      obtain ⟨h1, rfl⟩ := h
      rw [app_cons, ← ih, h1]
      exact cons_false_blank.symm
    · rw [strip, ite_eq_right_of_eq_false _ _ (eq_false h), app_cons, app_cons, ih]

theorem app_ones (n : Nat) : app (List.replicate n true) blank = Core.ones n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, app_cons, ih]; rfl

/-- A bounded run from blank tape in state `q` that ends at an E-event, checked on the list simulator. -/
theorem blank_reaches_E (q : Core.St) (t : Nat) (c : List Bool) (n : Nat)
    (h : (TM.fsteps trans t (FCfg.blank q)).map (fun d => (strip d.l, strip d.r, d.st)) =
      some (c.reverse, List.replicate n true, Core.St.E)) :
    steps t (blankCfg q) = some (Core.Ev c n) := by
  cases e : TM.fsteps trans t (FCfg.blank q) with
  | none => rw [e] at h; cases h
  | some d =>
    rw [e] at h
    obtain ⟨l, r, s⟩ := d
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hl, hr, rfl⟩ := h
    have h2 := blank_reaches trans e
    show TM.steps trans t (blankCfg q) = _
    rw [h2]
    simp only [FCfg.toCfg, Core.Ev, Core.EvT]
    rw [← app_strip l, ← app_strip r, hl, hr, app_ones]

end VRB
