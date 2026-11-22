import Machine

/-!
# 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF: the only way into the halt

The machine halts when C reads 1.  Walking back through the table, the last four steps before a halt are forced:

* C is entered only by B0 (`1RC`), so B read 0 with a 1 beyond it;
* B is entered by A0 (`1RB`) or E1 (`0LB`); E1 moves left and leaves a 0 where C would look, so it is A0, which
  read 0 with `0 1` beyond;
* A is entered only by E0 (`1RA`), so E read 0 with `0 0 1` beyond (`pre_halt`);
* E is entered by A1, D0 or F0; D0 (`1LE`) moves left and writes a 1 next to E's cell, so it is A1 or F0, and the
  machine was moving right (`pre_halt_from`).

So a halt needs E, moving right, to read `0 0 0 1`: three blank cells and then a 1.  In the engine's orientation
(PR 93's table W, mirrored) this is B moving left onto `1 0 0 0`.  Every D step of W that reads 0 right after B1
(`0RD`, the D steps of all the raw stretches logged so far, see `../raw/README.md`) has the 0 B just wrote beside it,
so it cannot be this route.
-/

namespace H50436

open TM

/-- The three steps before any halt: E reads `0 0 0 1`. -/
theorem pre_halt (c0 c1 c2 c3 : Config) (h0 : step c0 = some c1) (h1 : step c1 = some c2)
    (h2 : step c2 = some c3) (h3 : step c3 = none) :
    c0.st = .E ∧ c0.r 0 = false ∧ c0.r 1 = false ∧ c0.r 2 = false ∧ c0.r 3 = true := by
  obtain ⟨l0, r0, q0⟩ := c0
  obtain ⟨l1, r1, q1⟩ := c1
  obtain ⟨l2, r2, q2⟩ := c2
  obtain ⟨l3, r3, q3⟩ := c3
  simp only [step, TM.step] at h0 h1 h2 h3
  -- c3: C reading 1
  have hc3 : q3 = .C ∧ r3 0 = true := by
    cases q3 <;> cases hr : r3 0 <;> simp_all [trans]
  obtain ⟨rfl, hr3⟩ := hc3
  -- c2: B reading 0, moving right
  have hc2 : q2 = .B ∧ r2 0 = false ∧ r3 = tail r2 := by
    cases q2 <;> cases hr : r2 0 <;> simp [trans, hr] at h2 <;> (try obtain ⟨-, rfl, -⟩ := h2) <;> simp_all
  obtain ⟨rfl, hr2, rfl⟩ := hc2
  -- c1: A reading 0 (E1 would leave a 0 under C)
  have hc1 : q1 = .A ∧ r1 0 = false ∧ r2 = tail r1 := by
    cases q1 <;> cases hr : r1 0 <;> simp [trans, hr] at h1 <;> (try obtain ⟨-, rfl, -⟩ := h1) <;>
      simp_all [tail, cons]
  obtain ⟨rfl, hr1, rfl⟩ := hc1
  -- c0: E reading 0
  have hc0 : q0 = .E ∧ r0 0 = false ∧ r1 = tail r0 := by
    cases q0 <;> cases hr : r0 0 <;> simp [trans, hr] at h0 <;> (try obtain ⟨-, rfl, -⟩ := h0) <;>
      simp_all [tail]
  obtain ⟨rfl, hr0, rfl⟩ := hc0
  simp_all [tail]

/-- One step further back: the step into that E came from A1 or F0, moving right (D0 would write a 1 beside it). -/
theorem pre_halt_from (cm c0 c1 c2 c3 : Config) (hm : step cm = some c0) (h0 : step c0 = some c1)
    (h1 : step c1 = some c2) (h2 : step c2 = some c3) (h3 : step c3 = none) :
    (cm.st = .A ∧ cm.r 0 = true ∨ cm.st = .F ∧ cm.r 0 = false) ∧ c0.r = tail cm.r := by
  obtain ⟨hq, -, hb, -, -⟩ := pre_halt c0 c1 c2 c3 h0 h1 h2 h3
  obtain ⟨lm, rm, qm⟩ := cm
  obtain ⟨l0, r0, q0⟩ := c0
  simp only at hq hb
  subst hq
  simp only [step, TM.step] at hm
  cases qm <;> cases hr : rm 0 <;> simp [trans, hr] at hm <;> (try obtain ⟨-, rfl, -⟩ := hm) <;>
    simp_all [tail, cons]

end H50436
