import CarryData

/-!
# The digit carry rule, as a model (24 November 2026)

From step 2·10^7 on, at each visit of the head of 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE in state C to the left
end, the tape is `C>0 (01101)^n W` with `W` = a fixed head part of 44 cells, 46 digits of 25 cells
(`a110 b110 c011 0011 0d11 0e11 0`, five free cells each) and a fixed end.  Between two such visits the head makes
15 trips into the digits; trip p (p = 0..14) feeds carry Y into digit 0 if p is 1, 6 or 11 and carry X otherwise,
and a carry reaching a digit rewrites it and passes a carry on or stops, by the table `tab` (73 entries,
`CarryData.lean`, written by `py/carry.py lean`).

This file is about that **model**, not about the machine.  The link to the machine is computed, not proved:
`py/carry.py trips` checks the table trip by trip against the machine on the first 300 sweeps, and
`py/carry.py check` checks it sweep by sweep against all 29,299 walls from step 2·10^7 to 2·10^10.

What is proved here: the model never needs an entry that the table does not have.  `Good p l` says that digit 0
of `l` is in the set `fmask[p]` and that every two neighbouring digits of `l` are in the set `pmask` (240 pairs).
`trip_good`: trip p maps a `Good p` string either to a `Good (p+1 mod 15)` string, or the carry passes the last
digit (`off`: it reaches the end of the wall); it never meets a pair (carry, digit) outside the table (`stuck`).
This holds for strings of every length.  `wall0_never_stuck`: from the 46 digits of the wall at step 20,018,306,
any number of trips of the model never get stuck.  Everything is checked by `decide`; kernel only.
-/

namespace H30773.Carry

/-- The table entry for carry `c` reaching digit `x`, if there is one. -/
def look (c x : Nat) : Option (Nat × Nat) :=
  if c < 6 ∧ x < 32 then (tab.getD c []).getD x none else none

/-- Digit `y` may stand right of digit `x`. -/
def pairOK (x y : Nat) : Bool := x < 32 && y < 32 && (pmask.getD x 0 >>> y) % 2 == 1

/-- Digit 0 may be `x` at the start of trip `p`. -/
def firstOK (p x : Nat) : Bool := x < 32 && (fmask.getD p 0 >>> x) % 2 == 1

/-- The carry that trip `p` feeds into digit 0: Y (2) for p = 1, 6, 11, else X (1). -/
def cin (p : Nat) : Nat := if p = 1 ∨ p = 6 ∨ p = 11 then 2 else 1

/-- The outcome of a trip on a digit string. -/
inductive Res where
  | ok (l : List Nat)
  | off
  | stuck

/-- One trip: carry `c` enters the first digit of the list. -/
def run (c : Nat) : List Nat → Res
  | [] => if c = 0 then .ok [] else .off
  | d :: l =>
    if c = 0 then .ok (d :: l) else
      match look c d with
      | none => .stuck
      | some (d', c') =>
        match run c' l with
        | .ok l' => .ok (d' :: l')
        | r => r

/-- Every two neighbouring digits are allowed. -/
def chainOK : List Nat → Bool
  | a :: b :: l => pairOK a b && chainOK (b :: l)
  | _ => true

/-- The digit strings at the start of trip `p`. -/
def Good (p : Nat) : List Nat → Prop
  | [] => False
  | x :: l => firstOK p x = true ∧ chainOK (x :: l) = true

/-! ## The finite checks -/

/-- Carry `c` reaching digit `x` with right neighbour `y`: the new pair is allowed, and the carry passed on (if
any) has an entry for `y`. -/
def stepOK (c x y : Nat) : Bool :=
  match look c x with
  | none => true
  | some (x2, c2) =>
    !pairOK x y ||
      (if c2 = 0 then pairOK x2 y else
        match look c2 y with
        | none => false
        | some (y2, _) => pairOK x2 y2)

/-- Digit 0 at the start of trip `p`: the trip's carry has an entry for it, and the new digit 0 is allowed at
the start of the next trip. -/
def firstStepOK (p x : Nat) : Bool :=
  !firstOK p x ||
    (match look (cin p) x with
     | none => false
     | some (x2, _) => firstOK ((p + 1) % 15) x2)

theorem certStep : ((List.range 6).all fun c => (List.range 32).all fun x =>
    (List.range 32).all fun y => stepOK c x y) = true := by decide

theorem certFirst : ((List.range 15).all fun p => (List.range 32).all fun x => firstStepOK p x) = true := by
  decide

theorem certZero : ((List.range 32).all fun x => (look 0 x).isNone) = true := by decide

theorem stepOK_of {c x y : Nat} (hc : c < 6) (hx : x < 32) (hy : y < 32) : stepOK c x y = true := by
  have h := certStep
  simp only [List.all_eq_true, List.mem_range] at h
  exact h c hc x hx y hy

theorem firstStepOK_of {p x : Nat} (hp : p < 15) (hx : x < 32) : firstStepOK p x = true := by
  have h := certFirst
  simp only [List.all_eq_true, List.mem_range] at h
  exact h p hp x hx

theorem look_bounds {c x : Nat} {v : Nat × Nat} (h : look c x = some v) : c < 6 ∧ x < 32 := by
  unfold look at h
  split at h
  · assumption
  · cases h

theorem look_ne_zero {c x : Nat} {v : Nat × Nat} (h : look c x = some v) : c ≠ 0 := by
  intro hc
  subst hc
  have hx := (look_bounds h).2
  have hz := certZero
  simp only [List.all_eq_true, List.mem_range] at hz
  have := hz x hx
  rw [h] at this
  cases this

theorem pairOK_bounds {x y : Nat} (h : pairOK x y = true) : x < 32 ∧ y < 32 := by
  unfold pairOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2⟩

theorem firstOK_bound {p x : Nat} (h : firstOK p x = true) : x < 32 := by
  unfold firstOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem run_zero (l : List Nat) : run 0 l = .ok l := by
  cases l <;> simp [run]

theorem run_cons {c d d' c' : Nat} {l : List Nat} (hc : c ≠ 0) (h : look c d = some (d', c')) :
    run c (d :: l) = (match run c' l with
      | .ok l' => .ok (d' :: l')
      | r => r) := by
  simp only [run, hc, h, ite_false]

/-! ## The trips -/

/-- A carry that has an entry for digit `x` either runs off the end or leaves an allowed string that starts with
the new digit. -/
theorem runA : ∀ (l : List Nat) (c x x2 c2 : Nat), look c x = some (x2, c2) → chainOK (x :: l) = true →
    run c (x :: l) = .off ∨ ∃ l', run c (x :: l) = .ok (x2 :: l') ∧ chainOK (x2 :: l') = true := by
  intro l
  induction l with
  | nil =>
    intro c x x2 c2 h _
    have hc := look_ne_zero h
    by_cases h2 : c2 = 0
    · subst h2
      right
      exact ⟨[], by simp [run, hc, h], rfl⟩
    · left
      simp [run, hc, h, h2]
  | cons y l ih =>
    intro c x x2 c2 h hch
    have hc := look_ne_zero h
    have hb := look_bounds h
    simp only [chainOK, Bool.and_eq_true] at hch
    obtain ⟨hxy, hrest⟩ := hch
    have hy := (pairOK_bounds hxy).2
    have hs := stepOK_of hb.1 hb.2 hy
    unfold stepOK at hs
    rw [h] at hs
    simp only [hxy, Bool.not_true, Bool.false_or] at hs
    by_cases h2 : c2 = 0
    · subst h2
      simp only [ite_true] at hs
      right
      refine ⟨y :: l, ?_, ?_⟩
      · simp [run, hc, h]
      · simp [chainOK, hs, hrest]
    · simp only [h2, ite_false] at hs
      cases hl : look c2 y with
      | none => rw [hl] at hs; cases hs
      | some v =>
        obtain ⟨y2, c3⟩ := v
        rw [hl] at hs
        rcases ih c2 y y2 c3 hl hrest with hoff | ⟨l', hok, hch'⟩
        · left
          rw [run_cons hc h, hoff]
        · right
          refine ⟨y2 :: l', ?_, ?_⟩
          · rw [run_cons hc h, hok]
          · simp only [chainOK, Bool.and_eq_true]
            exact ⟨hs, hch'⟩

/-- **Trip `p` keeps the strings good**: it never meets a pair (carry, digit) outside the table. -/
theorem trip_good (p : Nat) (hp : p < 15) (l : List Nat) (hl : Good p l) :
    run (cin p) l = .off ∨ ∃ l', run (cin p) l = .ok l' ∧ Good ((p + 1) % 15) l' := by
  cases l with
  | nil => cases hl
  | cons x l =>
    obtain ⟨hf, hch⟩ := hl
    have hfs := firstStepOK_of hp (firstOK_bound hf)
    unfold firstStepOK at hfs
    simp only [hf, Bool.not_true, Bool.false_or] at hfs
    cases hlk : look (cin p) x with
    | none => rw [hlk] at hfs; cases hfs
    | some v =>
      obtain ⟨x2, c2⟩ := v
      rw [hlk] at hfs
      rcases runA l (cin p) x x2 c2 hlk hch with hoff | ⟨l', hok, hch'⟩
      · exact Or.inl hoff
      · exact Or.inr ⟨x2 :: l', hok, hfs, hch'⟩

/-- `k` trips of the model from trip number `p`. -/
def trips : Nat → Nat → List Nat → Res
  | 0, _, l => .ok l
  | k + 1, p, l =>
    match run (cin p) l with
    | .ok l' => trips k ((p + 1) % 15) l'
    | r => r

theorem trips_never_stuck : ∀ (k p : Nat) (l : List Nat), p < 15 → Good p l → trips k p l ≠ .stuck := by
  intro k
  induction k with
  | zero => intro p l _ _ h; cases h
  | succ k ih =>
    intro p l hp hl
    rcases trip_good p hp l hl with hoff | ⟨l', hok, hg⟩
    · simp [trips, hoff]
    · simp only [trips, hok]
      exact ih _ _ (Nat.mod_lt _ (by decide)) hg

theorem wall0_good : Good 0 wall0 := by
  unfold wall0
  exact ⟨by decide, by decide⟩

/-- **From the wall at step 20,018,306, the model never gets stuck**, at any number of trips: until a carry runs
off the 46 digits, every trip finds its entries in the table. -/
theorem wall0_never_stuck (k : Nat) : trips k 0 wall0 ≠ .stuck :=
  trips_never_stuck k 0 wall0 (by decide) wall0_good

end H30773.Carry
