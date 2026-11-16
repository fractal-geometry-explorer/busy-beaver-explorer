import Machine

/-!
# The twin is the same machine, started in another state

`trans1` is the table of 1RB1LD_0LC1RC_1RA1RD_1LE0RB_---1LF_0LC0LA (bbchallenge id 176216), written on the same
state names.  Renaming this machine's states by `ren` (A → C, B → A, C → B; D, E, F fixed) turns this machine's
table into `trans1`, entry for entry (`sim_step`).  So the two machines make the same runs, step for step, and
this machine halts from blank tape exactly when 176216 halts from blank tape started in state C (`twin`).
-/

namespace H18397

open TM

/-- The table of 1RB1LD_0LC1RC_1RA1RD_1LE0RB_---1LF_0LC0LA. -/
def trans1 : St → Bool → Option (Bool × Dir × St)
  | .A, false => some (true, .R, .B)
  | .A, true => some (true, .L, .D)
  | .B, false => some (false, .L, .C)
  | .B, true => some (true, .R, .C)
  | .C, false => some (true, .R, .A)
  | .C, true => some (true, .R, .D)
  | .D, false => some (true, .L, .E)
  | .D, true => some (false, .R, .B)
  | .E, false => none
  | .E, true => some (true, .L, .F)
  | .F, false => some (false, .L, .C)
  | .F, true => some (false, .L, .A)

/-- The renaming of this machine's states to 176216's. -/
def ren : St → St
  | .A => .C
  | .B => .A
  | .C => .B
  | .D => .D
  | .E => .E
  | .F => .F

/-- A configuration of this machine read as one of 176216. -/
def φ (c : Cfg St) : Cfg St := ⟨c.l, c.r, ren c.st⟩

/-- One step of this machine is one step of 176216 on the renamed configuration. -/
theorem sim_step (c : Cfg St) : TM.step trans1 (φ c) = (TM.step trans c).map φ := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h : r 0 <;> simp [TM.step, trans1, trans, φ, ren, h]

theorem sim_steps : ∀ (n : Nat) (c : Cfg St), TM.steps trans1 n (φ c) = (TM.steps trans n c).map φ
  | 0, c => rfl
  | n + 1, c => by
    cases hs : TM.step trans c with
    | none =>
      have h1 : TM.step trans1 (φ c) = none := by rw [sim_step, hs]; rfl
      simp [TM.steps, hs, h1]
    | some d =>
      have h1 : TM.step trans1 (φ c) = some (φ d) := by rw [sim_step, hs]; rfl
      rw [TM.steps_succ_of_step trans n hs, TM.steps_succ_of_step trans1 n h1]
      exact sim_steps n d

/-- This machine halts from a configuration exactly when 176216 halts from its renaming. -/
theorem halts_iff (c : Cfg St) : TM.Halts trans c ↔ TM.Halts trans1 (φ c) := by
  constructor
  · rintro ⟨n, c', h, h'⟩
    refine ⟨n, φ c', ?_, ?_⟩
    · rw [sim_steps, h]; rfl
    · rw [sim_step, h']; rfl
  · rintro ⟨n, c', h, h'⟩
    rw [sim_steps] at h
    cases e : TM.steps trans n c with
    | none => rw [e] at h; cases h
    | some d =>
      rw [e] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      rw [sim_step] at h'
      refine ⟨n, d, e, ?_⟩
      cases e2 : TM.step trans d with
      | none => rfl
      | some x => rw [e2] at h'; cases h'

/-- This machine halts from blank tape exactly when 176216 halts from blank tape started in state C. -/
theorem twin : HaltsFromBlank ↔ TM.Halts trans1 (TM.blankCfg .C) :=
  halts_iff (TM.blankCfg .A)

end H18397
