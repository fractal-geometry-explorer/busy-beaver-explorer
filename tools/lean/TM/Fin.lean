import TM.Basic

/-!
# Bounded runs by evaluation

A configuration with finitely many marked cells, kept as two lists, and a simulator on it that is proved to agree
with `steps`.  A bounded run from blank tape then becomes a computation that `decide` (checked by Lean's kernel) or
`native_decide` (compiled, so it trusts the compiler as well) can evaluate:

* `FCfg.steps_eq`: `steps δ n c.toCfg = (fsteps δ n c).map FCfg.toCfg`;
* `blank_reaches`: `fsteps δ n (FCfg.blank q) = some c` gives `steps δ n (blankCfg q) = some c.toCfg`;
* `blank_halts`: if moreover `fstep δ c = none`, the machine halts from blank tape (after `n + 1` steps in the
  bbchallenge count);
* `blank_runs`: `(fsteps δ n (FCfg.blank q)).isSome` gives a run of `n` steps without a halt.

The list form drops nothing: `toCfg` appends blank tape to each list.  Two `FCfg`s can stand for the same `Cfg`
(trailing `false`s), which is harmless since the theorems only go from `FCfg` to `Cfg`.
-/

namespace TM

variable {Q : Type}

/-- A configuration with finitely many cells written: left (nearest first), right (head on its first cell). -/
structure FCfg (Q : Type) where
  l : List Bool
  r : List Bool
  st : Q
  deriving DecidableEq, Repr

def FCfg.toCfg (c : FCfg Q) : Cfg Q := ⟨app c.l blank, app c.r blank, c.st⟩

def FCfg.blank (q : Q) : FCfg Q := ⟨[], [], q⟩

section
variable (δ : Q → Bool → Option (Bool × Dir × Q))

/-- One step on lists; `none` when the machine halts. -/
def fstep (c : FCfg Q) : Option (FCfg Q) :=
  match δ c.st (c.r.headD false) with
  | none => none
  | some (w, .R, s) => some ⟨w :: c.l, c.r.tail, s⟩
  | some (w, .L, s) => some ⟨c.l.tail, c.l.headD false :: w :: c.r.tail, s⟩

/-- `n` steps on lists (tail recursive, so long runs evaluate without deep recursion). -/
def fsteps : Nat → FCfg Q → Option (FCfg Q)
  | 0, c => some c
  | n + 1, c =>
    match fstep δ c with
    | none => none
    | some c' => fsteps n c'

theorem app_head (w : List Bool) : app w blank 0 = w.headD false := by
  cases w <;> rfl

theorem app_tail (w : List Bool) : tail (app w blank) = app w.tail blank := by
  cases w <;> rfl

theorem FCfg.step_eq (c : FCfg Q) : step δ c.toCfg = (fstep δ c).map FCfg.toCfg := by
  unfold step fstep FCfg.toCfg
  simp only [app_head]
  cases δ c.st (c.r.headD false) with
  | none => rfl
  | some t =>
    obtain ⟨w, d, s⟩ := t
    cases d
    · simp only [Option.map_some, app_cons, app_tail]
    · simp only [Option.map_some, app_cons, app_tail]

theorem FCfg.steps_eq (n : Nat) (c : FCfg Q) : steps δ n c.toCfg = (fsteps δ n c).map FCfg.toCfg := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [steps, fsteps, FCfg.step_eq]
    cases fstep δ c with
    | none => rfl
    | some c' => exact ih c'

theorem FCfg.blank_toCfg (q : Q) : (FCfg.blank q).toCfg = blankCfg q := rfl

theorem blank_reaches {q : Q} {n : Nat} {c : FCfg Q} (h : fsteps δ n (FCfg.blank q) = some c) :
    steps δ n (blankCfg q) = some c.toCfg := by
  rw [← FCfg.blank_toCfg, FCfg.steps_eq, h]; rfl

theorem blank_runs {q : Q} {n : Nat} (h : (fsteps δ n (FCfg.blank q)).isSome) :
    ∃ c, steps δ n (blankCfg q) = some c := by
  cases e : fsteps δ n (FCfg.blank q) with
  | none => rw [e] at h; cases h
  | some c => exact ⟨c.toCfg, blank_reaches δ e⟩

theorem blank_halts {q : Q} {n : Nat} {c : FCfg Q} (h : fsteps δ n (FCfg.blank q) = some c)
    (hc : fstep δ c = none) : Halts δ (blankCfg q) :=
  ⟨n, c.toCfg, blank_reaches δ h, by rw [FCfg.step_eq, hc]; rfl⟩

/-- Halts within the first `n` steps (bbchallenge count): the run of `n` steps is `none`. -/
theorem halts_of_fsteps_none {q : Q} {n : Nat} (h : fsteps δ n (FCfg.blank q) = none) :
    Halts δ (blankCfg q) := by
  induction n generalizing q with
  | zero => cases h
  | succ n ih =>
    have key : ∀ (m : Nat) (c : FCfg Q), fsteps δ m c = none → Halts δ c.toCfg := by
      intro m
      induction m with
      | zero => intro c h; cases h
      | succ m ihm =>
        intro c h
        simp only [fsteps] at h
        cases e : fstep δ c with
        | none => exact ⟨0, c.toCfg, rfl, by rw [FCfg.step_eq, e]; rfl⟩
        | some c' =>
          rw [e] at h
          obtain ⟨k, d, h₁, h₂⟩ := ihm c' h
          refine ⟨k + 1, d, ?_, h₂⟩
          rw [steps_succ_of_step δ k (by rw [FCfg.step_eq, e]; rfl)]
          exact h₁
    rw [← FCfg.blank_toCfg]
    exact key _ _ h
end

end TM
