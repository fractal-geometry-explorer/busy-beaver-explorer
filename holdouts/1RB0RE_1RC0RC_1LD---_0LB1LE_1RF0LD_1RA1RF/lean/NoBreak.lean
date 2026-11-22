import Twin
import watch.Race

/-!
# No break: the twin's list question settles this machine too

`Twin.lean` proves that this machine (1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF, "M") follows its twin
1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF ("T") step for step until the first *break*, T in B with a 1 in one of
the two cells ahead, and that neither halts if no break ever comes (`not_halts_of_noBreak`).  The halting
transitions do not correspond: T halts on `F> 0 0 1`, M on `F> 0 0 1 1` and `F> 0 0 0 1` (in T's terms).  So a
proof that T never halts does not by itself say that M never halts.

T's non-halting has been reduced to one question about a list program (`not_halts_of_arun` in T's `End.lean`: if
`arun k (.EO [true, false] none true)` is defined for every `k`, T never halts from blank tape).  This file shows that
the same hypothesis also rules out every break, so it settles M as well:

* `watch/Machine.lean` is T with a seventh state G watching the cell after `B> 0`: it halts exactly at a break.
* `watch/*.lean` are T's own files, copied unchanged by `py/port_watch.py`; they check for the watched table, so
  `H75625W.not_halts_of_arun` holds with the same list program (`H75625W.arun` is T's `arun`, word for word).
* `wsteps`: the watched twin runs T's run (G read as C).  `noBreak_of_watched`: if the watched twin never halts,
  T's run has no break.  `not_halts_of_arun`: under the list hypothesis neither M nor T halts from blank tape.

What is left is the same for both machines: that the list machine never fails (case 1 or 2 of T's `End.lean`).
-/

namespace H121862

open TM

/-- The watched twin's states read as the twin's: G is C. -/
def wst : H75625W.St → Twin.St
  | .A => .A
  | .B => .B
  | .C => .C
  | .D => .D
  | .E => .E
  | .F => .F
  | .G => .C

/-- A configuration of the watched twin read as one of the twin. -/
def wcfg (c : H75625W.Config) : Twin.Config := ⟨c.l, c.r, wst c.st⟩

/-- One step of the watched twin is one step of the twin. -/
theorem wstep {c c' : H75625W.Config} (h : H75625W.step c = some c') : Twin.step (wcfg c) = some (wcfg c') := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases hx : r 0 <;>
    simp [H75625W.step, TM.step, H75625W.trans, hx] at h <;> subst h <;>
    simp [Twin.step, TM.step, Twin.trans, wcfg, wst, hx]

/-- **The watched twin runs the twin's run.** -/
theorem wsteps (n : Nat) : ∀ {c c' : H75625W.Config}, H75625W.steps n c = some c' →
    Twin.steps n (wcfg c) = some (wcfg c') := by
  induction n with
  | zero => intro c c' h; simp at h; subst h; rfl
  | succ n ih =>
    intro c c' h
    cases hs : H75625W.step c with
    | none => simp [H75625W.steps, TM.steps, hs] at h
    | some d =>
      rw [H75625W.steps, TM.steps_succ_of_step _ n hs] at h
      rw [Twin.steps, TM.steps_succ_of_step _ n (wstep hs)]
      exact ih h

theorem steps_add {Q : Type} (δ : Q → Bool → Option (Bool × Dir × Q)) (a b : Nat) :
    ∀ c, TM.steps δ (a + b) c = (TM.steps δ a c).bind (TM.steps δ b) := by
  induction a with
  | zero => intro c; simp [TM.steps]
  | succ a ih =>
    intro c
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [e]
    cases hs : TM.step δ c with
    | none => simp [TM.steps, hs]
    | some d => rw [TM.steps_succ_of_step δ _ hs, TM.steps_succ_of_step δ _ hs]; exact ih d

/-- A run that is not defined ends in a halt. -/
theorem halts_of_none {Q : Type} (δ : Q → Bool → Option (Bool × Dir × Q)) (n : Nat) :
    ∀ c, TM.steps δ n c = none → TM.Halts δ c := by
  induction n with
  | zero => intro c h; simp [TM.steps] at h
  | succ n ih =>
    intro c h
    cases hs : TM.step δ c with
    | none => exact ⟨0, c, rfl, hs⟩
    | some d =>
      rw [TM.steps_succ_of_step δ n hs] at h
      obtain ⟨m, c', h1, h2⟩ := ih d h
      exact ⟨m + 1, c', by rw [TM.steps_succ_of_step δ m hs]; exact h1, h2⟩

theorem wcfg_init : wcfg H75625W.init = Twin.init := rfl

/-- **If the watched twin never halts, the twin's run has no break.** -/
theorem noBreak_of_watched (h : ¬ H75625W.HaltsFromBlank) : NoBreak := by
  intro n c d hr _ hb
  have def_all : ∀ m, ∃ x, H75625W.steps m H75625W.init = some x := by
    intro m
    cases hm : H75625W.steps m H75625W.init with
    | none => exact absurd (halts_of_none _ m _ hm) h
    | some x => exact ⟨x, rfl⟩
  obtain ⟨x, hx⟩ := def_all n
  have hd : wcfg x = d := by
    have := wsteps n hx
    rw [wcfg_init, hr.1] at this
    exact (Option.some.inj this).symm
  obtain ⟨y, hy⟩ := def_all (n + 2)
  have h2 : H75625W.steps 2 x = some y := by
    have := steps_add H75625W.trans n 2 H75625W.init
    simp only [H75625W.steps] at hy hx
    rw [hy, hx] at this
    simpa using this.symm
  obtain ⟨l, r, s⟩ := x
  subst hd
  obtain ⟨hB, h01⟩ := hb
  cases s <;> simp [wcfg, wst] at hB
  simp only [wcfg] at h01
  cases h0 : r 0 <;> cases h1 : r 1 <;> simp_all [H75625W.steps, TM.steps, TM.step, H75625W.trans, tail]

/-- **Under the twin's list hypothesis neither machine halts.**  `H75625W.arun` is the twin's `arun`, copied word for
word; so the statement that settles 1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF (its `not_halts_of_arun`) settles
1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF too. -/
theorem not_halts_of_arun (h : ∀ k, (H75625W.arun k (.EO [true, false] none true)).isSome) :
    ¬ HaltsFromBlank ∧ ¬ Twin.HaltsFromBlank :=
  not_halts_of_noBreak (noBreak_of_watched (H75625W.not_halts_of_arun h))

end H121862
