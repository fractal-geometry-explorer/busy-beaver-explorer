import Machine

/-!
# The twin is the same machine, started in another state

`trans1` is the table of 1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE (bbchallenge id 99198), written on the same state
names.  Renaming its states by `ren` (A → E, B → A, C → B, D → C, E → D, F → F) gives this machine's table except for
one entry: its `A1 → 1LE` becomes this machine's `E1 → 0LB`, and here `E1 → 0LB, B → (rewrite the cell) R C,
C0 → 1LD` takes three steps to do what `A1 → 1LE` does in one, whatever the cell to the left holds (`sim_step`).  So
every run of 99198 is a run of this machine with a few steps inserted, and the two halt together (`halts_iff`).
From blank tape this machine starts in A, which is 99198's B (`twin`): the twin question is whether 99198 halts when
started in state B on blank tape.
-/

namespace H97939

open TM

/-- The table of 1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE. -/
def trans1 : St → Bool → Option (Bool × Dir × St)
  | .A, false => some (true, .R, .B)
  | .A, true => some (true, .L, .E)
  | .B, false => some (true, .R, .C)
  | .B, true => some (true, .L, .F)
  | .C, false => some (false, .R, .D)
  | .C, true => some (true, .R, .D)
  | .D, false => some (true, .L, .E)
  | .D, true => some (false, .R, .E)
  | .E, false => some (false, .L, .A)
  | .E, true => some (false, .L, .B)
  | .F, false => none
  | .F, true => some (true, .L, .E)

/-- The renaming of 99198's states to this machine's. -/
def ren : St → St
  | .A => .E
  | .B => .A
  | .C => .B
  | .D => .C
  | .E => .D
  | .F => .F

/-- A configuration of 99198 read as one of this machine. -/
def φ (c : Cfg St) : Cfg St := ⟨c.l, c.r, ren c.st⟩

theorem cons_head_tail' (t : Tape) : cons (t 0) (tail t) = t := by
  funext n; cases n <;> rfl

/-- The two machines halt on the same configurations. -/
theorem sim_none (c : Cfg St) : TM.step trans1 c = none ↔ TM.step trans (φ c) = none := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h : r 0 <;> simp [TM.step, trans1, trans, φ, ren, h]

/-- One step of 99198 is one step of this machine, or three for `A1`. -/
theorem sim_step (c c' : Cfg St) (h : TM.step trans1 c = some c') :
    ∃ k, 1 ≤ k ∧ TM.steps trans k (φ c) = some (φ c') := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases hr : r 0 <;> simp [TM.step, trans1, hr] at h <;> subst h
  case A.true =>
    refine ⟨3, by omega, ?_⟩
    cases hl : l 0 <;> simp [TM.steps, TM.step, trans, φ, ren, hr, hl, cons] <;>
      (funext n; cases n <;> simp [hl])
  all_goals exact ⟨1, Nat.le_refl _, by simp [TM.steps, TM.step, trans, φ, ren, hr]⟩

/-- Every run of 99198 is matched by a run of this machine at least as long. -/
theorem sim_steps : ∀ (n : Nat) (c c' : Cfg St), TM.steps trans1 n c = some c' →
    ∃ m, n ≤ m ∧ TM.steps trans m (φ c) = some (φ c')
  | 0, c, c', h => by
    simp [TM.steps] at h; subst h; exact ⟨0, Nat.le_refl _, rfl⟩
  | n + 1, c, c', h => by
    cases hs : TM.step trans1 c with
    | none => simp [TM.steps, hs] at h
    | some d =>
      rw [TM.steps_succ_of_step trans1 n hs] at h
      obtain ⟨k, hk, hk'⟩ := sim_step c d hs
      obtain ⟨m, hm, hm'⟩ := sim_steps n d c' h
      exact ⟨k + m, by omega, TM.steps_seq trans hk' hm'⟩

theorem halts_of_none {δ : St → Bool → Option (Bool × Dir × St)} :
    ∀ (n : Nat) (c : Cfg St), TM.steps δ n c = none → TM.Halts δ c
  | 0, c, h => by simp [TM.steps] at h
  | n + 1, c, h => by
    cases hs : TM.step δ c with
    | none => exact ⟨0, c, rfl, hs⟩
    | some d =>
      rw [TM.steps_succ_of_step δ n hs] at h
      obtain ⟨k, e, he, he'⟩ := halts_of_none n d h
      exact ⟨k + 1, e, by rw [TM.steps_succ_of_step δ k hs]; exact he, he'⟩

/-- 99198 halts from a configuration exactly when this machine halts from its renaming. -/
theorem halts_iff (c : Cfg St) : TM.Halts trans1 c ↔ TM.Halts trans (φ c) := by
  constructor
  · rintro ⟨n, c', h, h'⟩
    obtain ⟨m, _, hm⟩ := sim_steps n c c' h
    exact ⟨m, φ c', hm, (sim_none c').1 h'⟩
  · intro h2
    refine Classical.byContradiction fun h1 => ?_
    have hall : ∀ n, ∃ c', TM.steps trans1 n c = some c' := by
      intro n
      cases e : TM.steps trans1 n c with
      | none => exact absurd (halts_of_none n c e) h1
      | some c' => exact ⟨c', rfl⟩
    refine TM.not_halts_of_forall trans ?_ h2
    refine TM.forall_of_unbounded trans (fun m => ∃ c', TM.steps trans m (φ c) = some c') ?_ (fun _ h => h)
    intro n
    obtain ⟨c', hc'⟩ := hall n
    obtain ⟨m, hm, hm'⟩ := sim_steps n c c' hc'
    exact ⟨m, hm, _, hm'⟩

/-- This machine halts from blank tape exactly when 99198 halts from blank tape started in state B. -/
theorem twin : HaltsFromBlank ↔ TM.Halts trans1 (TM.blankCfg .B) :=
  (halts_iff (TM.blankCfg .B)).symm

end H97939
