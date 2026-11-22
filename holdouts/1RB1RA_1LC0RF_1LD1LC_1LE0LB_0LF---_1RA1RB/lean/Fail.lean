import P75625.Race

/-!
# Where the list machine of the Pascal machine can fail

About `astep` of `P75625/End.lean` (the list machine of 1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF, which is also
this machine's, see `Mirror.lean`).  `astep` fails (`none`) in two cases: F reaching the blank end during a
crossing, and an even crossing bounce blocked by a far part that is not clean.  Proved here, for every state:

* `astep_T`, `astep_EO`: a turn with no lone 1 in the zone never fails;
* `astep_T2_end`: a crossing turn with a clean far part whose tape ends in one 1 never fails;
* `astep_endOne`: a plain or crossing turn whose tape ends in one 1 hands that on to the next state, so blank end
  (`r = false`) comes only after an `EO` turn (E reading the last 1), until a sweep next reaches the end;
* `astep_none`: so a failure happens only at a crossing turn with blank end, at an `EO` turn during a crossing, or at
  a crossing turn whose far part is not clean.

Written by hand for this folder and copied to the folder of 1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA--- by
`py/port_mirror.py`.  Kernel only.
-/

namespace H75625
open TM

/-- The tape ends in one 1 (or the head is on that last 1, `EO`). -/
def endOne : AS → Bool
  | .T _ _ _ r => r
  | .T2 _ _ _ _ r => r
  | .EO _ _ _ => true

theorem endS_some (W : List Bool) (e r : Bool) (p : Bool) : (endS W e r none p).isSome := by
  cases e <;> cases r <;> rfl

theorem endS_true (W : List Bool) (e : Bool) (Z : Option (List Bool)) (p : Bool) :
    (endS W e true Z p).isSome ∧ ∀ b, endS W e true Z p = some b → endOne b = true := by
  cases e <;> cases Z <;> simp [endS, endOne]

theorem fromSweep_none (p r : Bool) (x : List Bool × Bool × Option (List Bool)) : (fromSweep none p r x).isSome := by
  obtain ⟨W, e, o⟩ := x
  cases o
  · exact endS_some W e r p
  · rfl

theorem fromSweep_true (Z : Option (List Bool)) (p : Bool) (x : List Bool × Bool × Option (List Bool)) :
    (fromSweep Z p true x).isSome ∧ ∀ b, fromSweep Z p true x = some b → endOne b = true := by
  obtain ⟨W, e, o⟩ := x
  cases o with
  | none => exact endS_true W e Z p
  | some r' => cases Z <;> simp [fromSweep, endOne]

theorem coreP_some (w : List Bool) (p : Bool) (t : List Bool) (r : Bool) : (coreP w p t r).isSome :=
  fromSweep_none _ r _

theorem coreP_true (w : List Bool) (p : Bool) (t : List Bool) (b : AS) (h : coreP w p t true = some b) :
    endOne b = true :=
  (fromSweep_true none _ _).2 b h

/-- With the tape ending in one 1, a crossing bounce keeps it so (when it has a next state). -/
theorem coreO_true (O : List Bool) : ∀ (N : List Bool) (p : Bool) (t : List Bool) (b : AS),
    coreO N O p t true = some b → endOne b = true := by
  induction O with
  | nil =>
    intro N p t b h
    cases p
    · exact coreP_true _ _ _ b h
    · exact coreP_true _ _ _ b h
  | cons x O ih =>
    intro N p t b h
    cases x with
    | false => exact ih _ p t b h
    | true =>
      simp only [coreO] at h
      split at h
      · exact (fromSweep_true _ _ _).2 b h
      · split at h
        · exact (fromSweep_true _ _ _).2 b h
        · cases h

/-- **A plain turn never fails** (`T`, and `EO` with no lone 1 in the zone). -/
theorem astep_T (w : List Bool) (p : Bool) (s : List Bool) (r : Bool) : (astep (.T w p s r)).isSome :=
  coreP_some _ _ _ _

theorem astep_EO (W : List Bool) (p : Bool) : (astep (.EO W none p)).isSome :=
  coreP_some _ _ _ _

/-- **A crossing turn with a clean far part and the tape ending in one 1 never fails.** -/
theorem astep_T2_end (N ws : List Bool) (p : Bool) (s : List Bool) :
    (astep (.T2 N (dbl (true :: ws)) p s true)).isSome := by
  have hf := far_even ws
  simp only [astep, dbl, two, List.cons_append, List.nil_append, coreO]
  simp only [dbl, two, List.cons_append, List.nil_append] at hf
  split
  · exact (fromSweep_true _ _ _).1
  · rw [hf]
    exact (fromSweep_true _ _ _).1

/-- **The end mark is kept.**  From a plain or crossing turn whose tape ends in one 1, every next state ends so too.
So a state with blank end (`r = false`) comes only from an `EO` turn (E on the last 1), and lasts until a sweep
next reaches the end. -/
theorem astep_endOne (a b : AS) (ha : endOne a = true) (hEO : ∀ W Z p, a ≠ .EO W Z p) (h : astep a = some b) :
    endOne b = true := by
  cases a with
  | T w p s r =>
    simp only [endOne] at ha; subst ha
    exact coreP_true _ _ _ b h
  | T2 N O p s r =>
    simp only [endOne] at ha; subst ha
    exact coreO_true O N p _ b h
  | EO W Z p => exact absurd rfl (hEO W Z p)

/-- **Where the list machine can fail.**  `astep b = none` only at a crossing turn with blank end, at `EO` during a
crossing (E on the last 1 with a lone 1 in the zone), or at a crossing turn whose far part is not clean. -/
theorem astep_none (b : AS) (h : astep b = none) :
    (∃ N O p s, b = .T2 N O p s false) ∨ (∃ W O p, b = .EO W (some O) p) ∨
      (∃ N O p s, b = .T2 N O p s true ∧ ∀ ws, O ≠ dbl (true :: ws)) := by
  cases b with
  | T w p s r =>
    have := astep_T w p s r
    rw [h] at this; cases this
  | T2 N O p s r =>
    cases r with
    | false => exact Or.inl ⟨N, O, p, s, rfl⟩
    | true =>
      refine Or.inr (Or.inr ⟨N, O, p, s, rfl, ?_⟩)
      intro ws hO
      subst hO
      have := astep_T2_end N ws p s
      rw [h] at this; cases this
  | EO W Z p =>
    cases Z with
    | none =>
      have := astep_EO W p
      rw [h] at this; cases this
    | some O => exact Or.inr (Or.inl ⟨W, O, p, rfl⟩)

end H75625
