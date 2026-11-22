import ZMap

/-!
# Following the exits of the region with the list simulator

`ZMap.lean` maps every start `Ev n (.Z k)` of the region (n < 12k + 12) to the next E-event, but that E-event has in
general a new tail word, not one of `1`, `X`, `Y`, `Z`.  This file is the machinery for a table of *fates* of
concrete starts (`ExitTab.lean`):

* `.halt`: the machine halts from `Ev n (.Z k)`;
* `.to n' T'`: the machine reaches the E-event `Ev n' T'` (a tail of the proved map) after at least one step.

`checkEntry` checks an entry with the list simulator of `TM/Fin.lean` (`runH` for a halt, `runTo` for an E-event:
it runs until the configuration *is* `Ev n' T'`);
`entry_sound` turns a checked table into these two statements.  `coverB` checks that a table has an entry for every
start of the region with k < K other than n = 2 and the halting family n = 12k + 9 (k odd), which ZMap.lean already
handles for every k.
-/

namespace H70770

open TM

/-- What becomes of a start of the region. -/
inductive Fate where
  | halt
  | to (n : Nat) (T : Tail)
  deriving DecidableEq, Repr

/-! ## Tapes as lists of cells -/

/-- The word `w` repeated `n` times, as a list. -/
def repL (n : Nat) (w : List Bool) : List Bool := (List.replicate n w).flatten

theorem app_append (u v : List Bool) (s : Tape) : app (u ++ v) s = app u (app v s) := (app_app u v s).symm

theorem rep_eq_app (n : Nat) (w : List Bool) (s : Tape) : rep n w s = app (repL n w) s := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repL, List.replicate_succ, List.flatten_cons, app_append, ih, rep_succ]

/-- The tail as a list of cells. -/
def tlL : Tail → List Bool
  | .one => [true]
  | .X k => [false, false, false] ++ repL k [true, false] ++ [true]
  | .Y k => [true, true] ++ repL k [false, true]
  | .Z k => [false, false, false] ++ repL k [true, false] ++ [false, false, false, true]

theorem tl_eq (T : Tail) : tl T = app (tlL T) blank := by
  cases T <;> simp [tl, tlL, rep_eq_app, app_append]

/-- The right side of `Ev n T` as a list of cells. -/
def evL (n : Nat) (T : Tail) : List Bool := repL 6 [false] ++ repL n [true, false] ++ tlL T

theorem Ev_eq (n : Nat) (T : Tail) : Ev n T = ⟨blank, app (evL n T) blank, .E⟩ := by
  simp only [Ev, evL, rep_eq_app, tl_eq, app_append]

/-- A side expanded into cells. -/
def flat : Side → List Bool
  | [] => []
  | (w, n) :: s => repL n w ++ flat s

theorem den_flat (s : Side) : den s = app (flat s) blank := by
  induction s with
  | nil => rfl
  | cons p s ih => obtain ⟨w, n⟩ := p; simp [den, flat, rep_eq_app, app_append, ih]

/-- Every run of the side is a word of 0s. -/
def allF (s : Side) : Bool := s.all fun p => p.1.all fun b => b == false

theorem app_falses (w : List Bool) (hw : (w.all fun b => b == false) = true) : app w blank = blank := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨rfl, hw⟩ := hw
    rw [app_cons, ih hw, cons_false_blank]

theorem rep_falses (n : Nat) (w : List Bool) (hw : (w.all fun b => b == false) = true) : rep n w blank = blank := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep_succ, ih, app_falses w hw]

theorem den_allF (s : Side) (h : allF s = true) : den s = blank := by
  induction s with
  | nil => rfl
  | cons p s ih =>
    obtain ⟨w, n⟩ := p
    simp only [allF, List.all_cons, Bool.and_eq_true] at h
    simp only [den_cons]
    rw [ih h.2]
    exact rep_falses n w h.1

/-- Trailing 0s dropped. -/
def dropZ : List Bool → List Bool
  | [] => []
  | b :: u => if dropZ u = [] ∧ b = false then [] else b :: dropZ u

theorem app_dropZ (u : List Bool) : app (dropZ u) blank = app u blank := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    simp only [dropZ]
    split
    · rename_i h
      obtain ⟨h1, rfl⟩ := h
      rw [h1] at ih
      rw [app_cons, ← ih]
      exact cons_false_blank.symm
    · rw [app_cons, app_cons, ih]

/-- The list configuration is the E-event `Ev n T`. -/
def isEv (n : Nat) (T : Tail) (c : FCfg St) : Bool :=
  decide (c.st = .E) && (c.l.all fun b => b == false) && decide (dropZ c.r = evL n T)

theorem isEv_spec {n : Nat} {T : Tail} {c : FCfg St} (h : isEv n T c = true) : c.toCfg = Ev n T := by
  obtain ⟨l, r, q⟩ := c
  simp only [isEv, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨rfl, hl⟩, hr⟩ := h
  rw [Ev_eq]
  unfold FCfg.toCfg
  simp only
  rw [app_falses l hl, ← app_dropZ, hr]

/-! ## Runs of the list simulator -/

/-- Run until the configuration is `Ev n T`, after at least one step. -/
def runTo (n : Nat) (T : Tail) : Nat → FCfg St → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, c, acc =>
    if decide (1 ≤ acc) && isEv n T c then true else
    match TM.fstep trans c with
    | none => false
    | some c' => runTo n T fuel c' (acc + 1)

theorem runTo_spec (n : Nat) (T : Tail) : ∀ (fuel : Nat) (c : FCfg St) (acc : Nat) (c₀ : Config),
    runTo n T fuel c acc = true → steps acc c₀ = some c.toCfg → ∃ m, 1 ≤ m ∧ steps m c₀ = some (Ev n T)
  | 0, c, acc, c₀, h, _ => by simp [runTo] at h
  | fuel + 1, c, acc, c₀, h, hr => by
    simp only [runTo] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact ⟨acc, hc.1, by rw [hr, isEv_spec hc.2]⟩
    · cases e : TM.fstep trans c with
      | none => rw [e] at h; cases h
      | some c' =>
        rw [e] at h
        refine runTo_spec n T fuel c' (acc + 1) c₀ h ?_
        have h1 : steps 1 c.toCfg = some c'.toCfg := by
          have hs : TM.step trans c.toCfg = some c'.toCfg := by rw [FCfg.step_eq, e]; rfl
          show TM.steps trans 1 _ = _
          rw [steps_succ_of_step trans 0 hs]; rfl
        exact steps_seq trans hr h1

/-- Run until a halt. -/
def runH : Nat → FCfg St → Bool
  | 0, _ => false
  | fuel + 1, c =>
    match TM.fstep trans c with
    | none => true
    | some c' => runH fuel c'

theorem runH_spec : ∀ (fuel : Nat) (c : FCfg St), runH fuel c = true → Halts trans c.toCfg
  | 0, c, h => by simp [runH] at h
  | fuel + 1, c, h => by
    simp only [runH] at h
    cases e : TM.fstep trans c with
    | none =>
      refine ⟨0, c.toCfg, rfl, ?_⟩
      rw [FCfg.step_eq, e]; rfl
    | some c' =>
      rw [e] at h
      obtain ⟨m, d, h1, h2⟩ := runH_spec fuel c' h
      have hs : TM.step trans c.toCfg = some c'.toCfg := by rw [FCfg.step_eq, e]; rfl
      exact ⟨m + 1, d, by rw [steps_succ_of_step trans m hs]; exact h1, h2⟩

/-- The E-event `Ev n T` as lists. -/
def startR (n : Nat) (T : Tail) : FCfg St := ⟨[], evL n T, .E⟩

theorem startR_eq (n : Nat) (T : Tail) : (startR n T).toCfg = Ev n T := by
  rw [Ev_eq]; rfl

/-! ## A table of fates -/

/-- Fuel for each run (an upper bound on the moves of the simulator, never reached). -/
def fuel : Nat := 10 ^ 11

/-- Check one entry (k, n, fate) for the start `Ev n (.Z k)`. -/
def checkEntry : Nat × Nat × Fate → Bool
  | (k, n, .halt) => runH fuel (startR n (.Z k))
  | (k, n, .to n' T') => runTo n' T' fuel (startR n (.Z k)) 0

/-- The fate the table gives to (k, n). -/
def lookup (k n : Nat) : List (Nat × Nat × Fate) → Option Fate
  | [] => none
  | (k', n', f) :: tab => if k' = k ∧ n' = n then some f else lookup k n tab

theorem lookup_mem (k n : Nat) (f : Fate) : ∀ tab, lookup k n tab = some f → (k, n, f) ∈ tab
  | [], h => by simp [lookup] at h
  | (k', n', f') :: tab, h => by
    simp only [lookup] at h
    split at h
    · rename_i hk
      obtain ⟨rfl, rfl⟩ := hk
      cases h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem k n f tab h)

theorem entry_halt {tab : List (Nat × Nat × Fate)} (hok : tab.all checkEntry = true) {k n : Nat}
    (h : lookup k n tab = some .halt) : Halts trans (Ev n (.Z k)) := by
  have hc := List.all_eq_true.mp hok _ (lookup_mem k n _ tab h)
  simp only [checkEntry] at hc
  have := runH_spec fuel _ hc
  rwa [startR_eq] at this

theorem entry_to {tab : List (Nat × Nat × Fate)} (hok : tab.all checkEntry = true) {k n n' : Nat} {T' : Tail}
    (h : lookup k n tab = some (.to n' T')) : ∃ m, 1 ≤ m ∧ steps m (Ev n (.Z k)) = some (Ev n' T') := by
  have hc := List.all_eq_true.mp hok _ (lookup_mem k n _ tab h)
  simp only [checkEntry] at hc
  have := runTo_spec n' T' fuel _ 0 (startR n (.Z k)).toCfg hc rfl
  rwa [startR_eq] at this

/-- The starts of the region that ZMap.lean handles for every k: n = 2, and the halting family. -/
def special (k n : Nat) : Bool := decide (n = 2) || decide (k % 2 = 1 ∧ n = 12 * k + 9)

/-- The table has an entry for every start of the region with k < K (and for Z_0 with n < 24), other than the
special ones. -/
def coverB (K : Nat) (tab : List (Nat × Nat × Fate)) : Bool :=
  (List.range K).all fun k => (List.range (max (12 * k + 12) 24)).all fun n =>
    special k n || !(decide (n < 12 * k + 12 ∨ k = 0)) || (lookup k n tab).isSome

theorem coverB_spec {K : Nat} {tab : List (Nat × Nat × Fate)} (h : coverB K tab = true) {k n : Nat} (hk : k < K)
    (hn : n < 12 * k + 12 ∨ (k = 0 ∧ n < 24)) (hs : special k n = false) : (lookup k n tab).isSome = true := by
  have h1 := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  have h2 := List.all_eq_true.mp h1 n (List.mem_range.mpr (by omega))
  simp only [hs, Bool.false_or, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h2
  rcases h2 with h2 | h2
  · exact absurd (by omega) h2
  · exact h2

end H70770
