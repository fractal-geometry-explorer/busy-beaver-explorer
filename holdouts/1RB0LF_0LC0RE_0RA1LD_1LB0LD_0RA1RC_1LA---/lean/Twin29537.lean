import Machine

/-!
# 1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD--- is this table, mirrored and started in state D

bbchallenge 29537 (1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---) is the table of this folder's machine (129771) read
in a mirror, with the states renamed: A, B, C, D, E, F of 29537 are D, B, C, A, E, F here (`is_mirror`).  So the
run of 29537 from blank tape is, cell for cell in the mirror, the run of this table from blank tape started in
state D (`mirror_steps'`, `halts_mirror'`), and

* `twin_halts_iff`: 29537 halts from blank tape if and only if this table halts from blank tape started in D;
* `twin_reach157`: that run is at a left record after 157 steps, `0^inf B> 0 (10)^3 0 0 (10) 1 (10) 1 (10) 1 (10)`,
  in block form `(3, o) (0, o) (1, i) (1, i) (1, i) (1, ·)`: the same kind of record as the records of this
  folder's own run.  From there `py/blockmm.py` (the block macro machine of this machine) reproduces 29537's run
  record for record (`py/twin.py`).

The table of 29537 is restated here (`H29537.trans`, the text of its generated `Machine.lean`), because the two
folders' modules cannot be imported together.  The mirror lemmas are those of `tools/lean/TM/Insert.lean`
(`mirrorCfg`, `step_mirrorCfg`), extended to runs here.  Written by hand; kernel only.
-/

namespace TM

section
variable {Q₁ Q₂ : Type} {δ₁ : Q₁ → Bool → Option (Bool × Dir × Q₁)} {δ₂ : Q₂ → Bool → Option (Bool × Dir × Q₂)}
  {φ : Q₂ → Q₁} [DecidableEq Q₂]

theorem mirror_steps' (hδ : ∀ q b, δ₁ (φ q) b = (δ₂ q b).map (fun t => (t.1, t.2.1.flip, φ t.2.2)))
    (n : Nat) (c : Cfg Q₂) : steps δ₁ n (mirrorCfg φ c) = (steps δ₂ n c).map (mirrorCfg φ) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [steps, step_mirrorCfg δ₂ δ₁ φ hδ c]
    cases step δ₂ c with
    | none => rfl
    | some c' => exact ih c'

/-- A machine halts from c exactly when its mirror image halts from the mirror image of c. -/
theorem halts_mirror' (hδ : ∀ q b, δ₁ (φ q) b = (δ₂ q b).map (fun t => (t.1, t.2.1.flip, φ t.2.2)))
    (c : Cfg Q₂) : Halts δ₂ c ↔ Halts δ₁ (mirrorCfg φ c) := by
  constructor
  · rintro ⟨n, c', hn, hs⟩
    exact ⟨n, mirrorCfg φ c', by rw [mirror_steps' hδ, hn]; rfl, by rw [step_mirrorCfg δ₂ δ₁ φ hδ, hs]; rfl⟩
  · rintro ⟨n, d, hn, hs⟩
    rw [mirror_steps' hδ] at hn
    cases hc : steps δ₂ n c with
    | none => rw [hc] at hn; cases hn
    | some c' =>
      rw [hc] at hn
      simp only [Option.map_some, Option.some.injEq] at hn
      subst hn
      rw [step_mirrorCfg δ₂ δ₁ φ hδ] at hs
      refine ⟨n, c', hc, ?_⟩
      cases hs' : step δ₂ c' with
      | none => rfl
      | some x => rw [hs'] at hs; cases hs

end

end TM

namespace H29537

open TM

/-- The states of 1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---. -/
inductive St where
  | A | B | C | D | E | F
  deriving DecidableEq, Repr

/-- The transition table of 1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---, as in its own `Machine.lean`. -/
def trans : St → Bool → Option (Bool × Dir × St)
  | .A, false => some (true, .R, .B)
  | .A, true => some (false, .R, .A)
  | .B, false => some (false, .R, .C)
  | .B, true => some (false, .L, .E)
  | .C, false => some (false, .L, .D)
  | .C, true => some (true, .R, .A)
  | .D, false => some (true, .L, .B)
  | .D, true => some (false, .R, .F)
  | .E, false => some (false, .L, .D)
  | .E, true => some (true, .L, .C)
  | .F, false => some (true, .R, .D)
  | .F, true => none

/-- The machine's text form. -/
def text : String := "1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---"

/-- The state of 129771's table that each state of 29537 is. -/
def toSt : St → H129771.St
  | .A => .D
  | .B => .B
  | .C => .C
  | .D => .A
  | .E => .E
  | .F => .F

theorem is_mirror : ∀ q b, H129771.trans (toSt q) b = (trans q b).map (fun t => (t.1, t.2.1.flip, toSt t.2.2)) := by
  intro q b
  cases q <;> cases b <;> rfl

end H29537

namespace H129771

open TM

theorem twin_blank : mirrorCfg H29537.toSt (blankCfg H29537.St.A) = blankCfg St.D := mirrorCfg_blank _ _

/-- **29537 is this table started in D.**  1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD--- halts from blank tape if and
only if 1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA--- halts from blank tape started in state D. -/
theorem twin_halts_iff : Halts H29537.trans (blankCfg H29537.St.A) ↔ Halts trans (blankCfg St.D) := by
  rw [halts_mirror' H29537.is_mirror, twin_blank]

/-- Started in D, the table is at a left record after 157 steps: `0^inf B> 0 (10)^3 0 0 (10) 1 (10) 1 (10) 1 (10)`. -/
theorem twin_reach157 : steps 157 (blankCfg St.D) =
    some ⟨blank, app [false, true, false, true, false, true, false, false, false, true, false, true, true, false,
      true, true, false, true, true, false] blank, .B⟩ :=
  blank_reaches trans (q := St.D) (n := 157)
    (c := ⟨[], [false, true, false, true, false, true, false, false, false, true, false, true, true, false,
      true, true, false, true, true, false], .B⟩) (by decide +kernel)

/-- So 29537 halts from blank tape exactly when this table halts from that record. -/
theorem twin_halts_iff_record : Halts H29537.trans (blankCfg H29537.St.A) ↔
    Halts trans ⟨blank, app [false, true, false, true, false, true, false, false, false, true, false, true, true, false,
      true, true, false, true, true, false] blank, .B⟩ := by
  rw [twin_halts_iff]
  exact halts_iff_of_steps' trans twin_reach157

end H129771
