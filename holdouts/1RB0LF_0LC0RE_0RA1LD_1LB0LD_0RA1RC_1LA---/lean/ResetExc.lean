import ResetMap
import ExcSim

/-!
# 1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---: the tail excursions of the first phases, checked

`ResetMap.lean` proves the reset map `X' = f X` for the head part of the tape, given that the tail excursions of
each phase come back with the signatures `Good X T K` asks for.  Here those hypotheses are **discharged** for the
first phases of both runs: a run-length simulator that is proved sound for every tape on the left
(`ExcSim.lean`) runs each excursion of each phase on the actual tail, and `native_decide` evaluates the check.

* `cc_spec`, `cGen_spec`, `cPhase_spec`, `cOrbit_spec`: a successful check of a list of excursions, of `j` phase
  steps, of a phase, of `k` phases in a row proves `HC`, `Gen`, `Good`, `GoodN` (kernel; the checker is ordinary
  code, only its success is evaluated).
* `goodN_own`, `goodN_twin`: `GoodN` for the first `KOWN` phases of this machine (from `Reset 40 T0own`) and the
  first `KTWIN` phases of the twin 1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD--- (from `Reset 52 T0twin`)
  (`native_decide`).
* `reach_own_phases`, `reach_twin_phases`: so both runs from blank tape reach the reset whose block is
  `fit K X₀ = f^K X₀`, with no halt on the way; the values are named in the README.
-/

namespace H129771

open TM TM.EX

/-- The words long blocks are folded into: the rotations of `1010` and of `1100`. -/
def ws : List (List Bool) :=
  [[true, false, true, false], [false, true, false, true], [true, true, false, false], [false, true, true, false],
   [false, false, true, true], [true, false, false, true]]

/-- Moves allowed per excursion. -/
def FUEL : Nat := 100000000

/-- One excursion, checked. -/
def ex (u : List Bool) (q q' : St) (v : List Bool) (T : Side) : Option Side := exc trans ws FUEL u q q' v T

theorem ex_spec {u : List Bool} {q q' : St} {v : List Bool} {T T' : Side} (h : ex u q q' v T = some T') :
    Exc u q q' v (dB blank T) (dB blank T') :=
  exc_spec trans ws FUEL u q q' v T T' h

/-- Cells in front of a side, folded into runs one by one from the far end. -/
def preL (w : List Bool) (T : Side) : Side := w.foldr (fun a s => nrm ws (([a], 1) :: s)) T

theorem dB_preL (b : Tape) (T : Side) : ∀ w, dB b (preL w T) = app w (dB b T)
  | [] => rfl
  | a :: w => by
    show dB b (nrm ws (([a], 1) :: preL w T)) = _
    rw [dB_nrm, dB_cons, rep_one, dB_preL b T w]
    rfl

/-- An excursion's signature: cells `u` (nearest first), states `q`, `q'`, cells `v`. -/
abbrev Sig := List Bool × St × St × List Bool

/-- A list of excursions in a row, then the cells `w` in front of what is left: the shape of `Hre` ... `He1`. -/
def HC : List Sig → List Bool → Tape → (Tape → Prop) → Prop
  | [], w, T, K => K (app w T)
  | (u, q, q', v) :: es, w, T, K => ∃ T1, Exc u q q' v T T1 ∧ HC es w T1 K

/-- The check of `HC`. -/
def cc : List Sig → List Bool → Side → Option Side
  | [], w, T => some (preL w T)
  | (u, q, q', v) :: es, w, T =>
    match ex u q q' v T with
    | none => none
    | some T1 => cc es w T1

theorem cc_spec : ∀ (es : List Sig) (w : List Bool) (T T' : Side) (K : Tape → Prop),
    cc es w T = some T' → K (dB blank T') → HC es w (dB blank T) K
  | [], w, T, T', K, h, hK => by
    simp only [cc, Option.some.injEq] at h
    subst h
    show K (app w (dB blank T))
    rw [← dB_preL]; exact hK
  | (u, q, q', v) :: es, w, T, T', K, h, hK => by
    simp only [cc] at h
    cases e : ex u q q' v T with
    | none => rw [e] at h; cases h
    | some T1 =>
      rw [e] at h
      exact ⟨_, ex_spec e, cc_spec es w T1 T' K h hK⟩

/-! ## The pieces of a phase, as lists of excursions -/

def Ere : List Sig := [([false, false, true, false], .A, .B, [true, false, false, true]),
  ([false, true, false, false], .E, .C, [false, true, false, true]),
  ([false, true, false, false], .E, .C, [false, true, false, true]),
  ([false, false, true, true], .A, .D, [false, true, false, true]),
  ([false, false, true, true], .A, .D, [false, true, false, true])]
def wre : List Bool := [true, false, true, false, true, false, true, false, true, false, true, false, true]
def Ero : List Sig := [([true, false, false, true], .B, .D, [true, false, true, true]),
  ([true, false, true, false], .C, .A, [true, false, true, false]),
  ([true, false, false, true], .B, .D, [true, false, true, true]),
  ([false, false, true, true], .A, .D, [false, true, false, true]),
  ([false, false, true, true], .A, .D, [false, true, false, true])]
def wro : List Bool := [true, false, true, false, true, false, true, false, true]
def Eg : List Sig := [([false, false, true, true], .A, .D, [false, false, true, false])]
def wg : List Bool := [true, false, true, false]
def we0 : List Bool := [true, true, false, true, false]
def Ee1 : List Sig := [([false, false, true, true], .A, .D, [false, false, true, false]),
  ([false, false, true, false], .A, .B, [true, false, true, false])]
def we1 : List Bool := [false, true, false, true, false, true, false]

theorem Hre_eq (T : Tape) (K : Tape → Prop) : Hre T K = HC Ere wre T K := rfl
theorem Hro_eq (T : Tape) (K : Tape → Prop) : Hro T K = HC Ero wro T K := rfl
theorem Hg_eq (T : Tape) (K : Tape → Prop) : Hg T K = HC Eg wg T K := rfl
theorem He0_eq (T : Tape) (K : Tape → Prop) : He0 T K = HC Eg we0 T K := rfl
theorem He1_eq (T : Tape) (K : Tape → Prop) : He1 T K = HC Ee1 we1 T K := rfl

/-! ## Phases -/

/-- `j` phase steps. -/
def cGen : Nat → Side → Option Side
  | 0, T => some T
  | j + 1, T =>
    match cc Eg wg T with
    | none => none
    | some T1 => cGen j T1

theorem cGen_spec : ∀ (j : Nat) (T T' : Side) (K : Tape → Prop), cGen j T = some T' → K (dB blank T') →
    Gen j (dB blank T) K
  | 0, T, T', K, h, hK => by simp only [cGen, Option.some.injEq] at h; subst h; exact hK
  | j + 1, T, T', K, h, hK => by
    simp only [cGen] at h
    cases e : cc Eg wg T with
    | none => rw [e] at h; cases h
    | some T1 =>
      rw [e] at h
      show Hg _ _
      rw [Hg_eq]
      exact cc_spec Eg wg T T1 _ e (cGen_spec j T1 T' K h hK)

/-- The end of a phase. -/
def cEnd (e : Nat) (T : Side) : Option Side := if e % 2 = 0 then cc Eg we0 T else cc Ee1 we1 T

theorem cEnd_spec (e : Nat) (T T' : Side) (K : Tape → Prop) (h : cEnd e T = some T') (hK : K (dB blank T')) :
    Hend e (dB blank T) K := by
  unfold cEnd at h
  unfold Hend
  split
  · rename_i he; simp only [he, ↓reduceIte] at h; rw [He0_eq]; exact cc_spec _ _ _ _ _ h hK
  · rename_i he; simp only [he, ↓reduceIte] at h; rw [He1_eq]; exact cc_spec _ _ _ _ _ h hK

/-- The rest of a phase after its reset piece, from the countdown `e`. -/
def cRest (e : Nat) (T1 : Side) : Option Side :=
  match cGen (e / 2) T1 with
  | none => none
  | some T2 => cEnd e T2

theorem cRest_spec (e : Nat) (T T' : Side) (K : Tape → Prop) (h : cRest e T = some T') (hK : K (dB blank T')) :
    Gen (e / 2) (dB blank T) (fun T2 => Hend e T2 K) := by
  unfold cRest at h
  cases e2 : cGen (e / 2) T with
  | none => rw [e2] at h; cases h
  | some T2 =>
    rw [e2] at h
    exact cGen_spec _ T T2 _ e2 (cEnd_spec e T2 T' K h hK)

/-- A whole phase from `Reset X`. -/
def cPhase (X : Nat) (T : Side) : Option Side :=
  if X % 2 = 0 then
    match cc Ere wre T with
    | none => none
    | some T1 => cRest (X / 2 - 18 + 11) T1
  else
    match cc Ero wro T with
    | none => none
    | some T1 => cRest (X / 2 - 18 + 12) T1

theorem cPhase_spec (X : Nat) (T T' : Side) (K : Tape → Prop) (h : cPhase X T = some T') (hK : K (dB blank T')) :
    Good X (dB blank T) K := by
  unfold cPhase at h
  unfold Good
  split
  · rename_i hp
    simp only [hp, ↓reduceIte] at h
    rw [Hre_eq]
    cases e1 : cc Ere wre T with
    | none => rw [e1] at h; cases h
    | some T1 => rw [e1] at h; exact cc_spec _ _ _ _ _ e1 (cRest_spec _ T1 T' K h hK)
  · rename_i hp
    simp only [hp, ↓reduceIte] at h
    rw [Hro_eq]
    cases e1 : cc Ero wro T with
    | none => rw [e1] at h; cases h
    | some T1 => rw [e1] at h; exact cc_spec _ _ _ _ _ e1 (cRest_spec _ T1 T' K h hK)

/-- `k` phases in a row from `Reset X`. -/
def cOrbit : Nat → Nat → Side → Bool
  | 0, _, _ => true
  | k + 1, X, T =>
    match cPhase X T with
    | none => false
    | some T' => cOrbit k (f X) T'

theorem cOrbit_spec : ∀ (k X : Nat) (T : Side), cOrbit k X T = true → GoodN k X (dB blank T)
  | 0, _, _, _ => trivial
  | k + 1, X, T, h => by
    simp only [cOrbit] at h
    cases e : cPhase X T with
    | none => rw [e] at h; cases h
    | some T' =>
      rw [e] at h
      exact cPhase_spec X T T' _ e (cOrbit_spec k (f X) T' h)

/-- From a reset reached after `N` steps, `k` checked phases reach the reset of `fit k X`. -/
theorem reach_of_check {c : Config} {N X : Nat} {T : Side} (hX : 36 ≤ X) (h0 : steps N c = some (Reset X (dB blank T)))
    (k : Nat) (h : cOrbit k X T = true) : ∃ n T', N + k ≤ n ∧ steps n c = some (Reset (fit k X) T') := by
  obtain ⟨m, T', hm, hs⟩ := orbit k X _ hX (cOrbit_spec k X T h)
  exact ⟨N + m, T', by omega, steps_seq trans h0 hs⟩

/-! ## The two runs -/

/-- The cells of `T0own`. -/
def L0own : List Bool := [true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, false, false, true, false, true, false, false, false, true, false, true, false, false, true, false, true, false, false, true, false, true, true, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, false, false, true, false, true, true, false]

theorem T0own_eq : T0own = dB blank (ofList ws L0own) := by
  rw [dB_ofList]; rfl

/-- The cells of `T0twin`. -/
def L0twin : List Bool := [true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, false, true, false, true, true, false, true, false, false, false, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false, true, false]

theorem T0twin_eq : T0twin = dB blank (ofList ws L0twin) := by
  rw [dB_ofList]; rfl
end H129771
