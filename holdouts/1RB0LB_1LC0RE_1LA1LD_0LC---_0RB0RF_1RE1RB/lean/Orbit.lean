import Map
import Blank

/-!
# The run from blank tape follows the E-event map

`blank_reaches_E`: from blank tape the machine reaches `Ecfg 4 124` after 9008 steps (the list simulator, evaluated
by the kernel).  From there every E-step with a positive counter is `emap` (`emap_sound`), so the run is the orbit of
`(4, 124)` under `emap` for as long as the counter stays positive (`orbit_sound`).  `orbit_kernel` and
`orbit_native` check that it does for the first 1,000 and 20,000 E-steps, which gives runs without a halt far longer
than any simulation (`no_halt_kernel`, `no_halt_native`; the step counts have more than 250 and 5,000 digits), and
`not_halts_of_good`: if the counter never runs out, the machine never halts.
-/

namespace H48788

open TM

/-! ## From lists to tapes -/

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

theorem app_replicate (n : Nat) (w : List Bool) (s : Tape) :
    app (List.replicate n w).flatten s = rep n w s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, ← app_app, ih]; rfl

/-- `Ecfg a m` as lists. -/
def EL (a m : Nat) : List Bool := (List.replicate (m + 1) [false]).flatten ++ (List.replicate a [true, false]).flatten ++ [false, true]

theorem app_EL (a m : Nat) : app (EL a m) blank = rep (m + 1) [false] (Ctr a) := by
  rw [EL, ← app_app, ← app_app, app_replicate, app_replicate]
  rfl

/-- After 9008 steps from blank tape: `1 0 0 (10)^4 0^124 E> 1`. -/
theorem blank_reaches_E : steps 9008 init = some (Ecfg 4 124) := by
  have h : (TM.fsteps trans 9008 (FCfg.blank St.A)).map (fun c => (strip c.l, strip c.r, c.st)) =
      some (EL 4 124, [true], St.E) := by decide +kernel
  cases e : TM.fsteps trans 9008 (FCfg.blank St.A) with
  | none => rw [e] at h; cases h
  | some c =>
    rw [e] at h
    obtain ⟨l, r, q⟩ := c
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hl, hr, rfl⟩ := h
    have h2 := blank_reaches trans e
    show TM.steps trans 9008 (blankCfg St.A) = _
    rw [h2]
    simp only [FCfg.toCfg, Ecfg]
    rw [← app_strip l, ← app_strip r, hl, hr, app_EL]
    rfl

/-! ## The orbit -/

/-- One E-step on (counter, gap, steps so far). -/
def ostep (x : Nat × Nat × Nat) : Nat × Nat × Nat :=
  ((emap x.1 x.2.1).1, (emap x.1 x.2.1).2.1, x.2.2 + (emap x.1 x.2.1).2.2)

/-- `n` E-steps. -/
def oiter : Nat → Nat × Nat × Nat → Nat × Nat × Nat
  | 0, x => x
  | n + 1, x => oiter n (ostep x)

/-- The counter is positive and the gap at least 2 for the next `n` E-steps. -/
def allGood : Nat → Nat × Nat × Nat → Bool
  | 0, _ => true
  | n + 1, x => (1 ≤ x.1 && 2 ≤ x.2.1) && allGood n (ostep x)

theorem orbit_sound : ∀ (n : Nat) (x : Nat × Nat × Nat), allGood n x = true →
    steps x.2.2 init = some (Ecfg x.1 x.2.1) →
    steps (oiter n x).2.2 init = some (Ecfg (oiter n x).1 (oiter n x).2.1) := by
  intro n
  induction n with
  | zero => intro x _ h; exact h
  | succ n ih =>
    intro x hg h
    simp only [allGood, Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨⟨ha, hm⟩, hg⟩ := hg
    apply ih (ostep x) hg
    exact steps_seq trans h (emap_sound x.1 x.2.1 ha hm)

/-- The E-configuration at step 9008. -/
def x0 : Nat × Nat × Nat := (4, 124, 9008)

theorem orbit_kernel : allGood 1000 x0 = true := by decide +kernel

theorem orbit_native : allGood 20000 x0 = true := by native_decide

/-- No halt in the first `(oiter 1000 x0).2.2` steps (a number of more than 250 digits), by the kernel. -/
theorem no_halt_kernel : ∃ c, steps (oiter 1000 x0).2.2 init = some c :=
  ⟨_, orbit_sound 1000 x0 orbit_kernel blank_reaches_E⟩

theorem kernel_bound : 10 ^ 250 < (oiter 1000 x0).2.2 := by decide +kernel

/-- No halt in the first `(oiter 20000 x0).2.2` steps (more than 5,000 digits), with `native_decide`. -/
theorem no_halt_native : ∃ c, steps (oiter 20000 x0).2.2 init = some c :=
  ⟨_, orbit_sound 20000 x0 orbit_native blank_reaches_E⟩

theorem native_bound : 10 ^ 5000 < (oiter 20000 x0).2.2 := by native_decide

theorem emap_pos (a m : Nat) : 1 ≤ (emap a m).2.2 := by
  unfold emap
  split
  · simp only; omega
  · split <;> (simp only; omega)

theorem oiter_ge : ∀ (n : Nat) (x : Nat × Nat × Nat), x.2.2 + n ≤ (oiter n x).2.2 := by
  intro n
  induction n with
  | zero => intro x; simp [oiter]
  | succ n ih =>
    intro x
    have h₁ := ih (ostep x)
    have h₂ := emap_pos x.1 x.2.1
    simp only [oiter, ostep] at h₁ ⊢
    omega

/-- **Halting needs the counter to run out**: if the orbit of `(4, 124)` under `emap` keeps a positive counter and
a gap of at least 2 forever, the machine never halts from blank tape. -/
theorem not_halts_of_good (h : ∀ n, allGood n x0 = true) : ¬ HaltsFromBlank := by
  apply not_halts_of_forall trans
  apply forall_of_unbounded trans (fun t => ∃ n, (oiter n x0).2.2 = t)
  · intro N
    exact ⟨(oiter N x0).2.2, by have := oiter_ge N x0; omega, N, rfl⟩
  · rintro t ⟨n, rfl⟩
    exact ⟨_, orbit_sound n x0 (h n) blank_reaches_E⟩

end H48788
