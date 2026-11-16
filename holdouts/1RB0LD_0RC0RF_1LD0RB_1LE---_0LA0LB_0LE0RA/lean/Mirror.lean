import Machine
import MachineM

/-!
# 1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA is a mirror image

The table of 1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA is the table of `MachineM.lean`
(1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD) with left and right exchanged and the states renamed by `τ`
(`trans_tau`).  The map `φ` turns a configuration into its mirror image (the head stays on the same cell), and it
commutes with a step (`step_phi`), so with runs (`steps_phi`).  The blank tape in state A goes to the blank tape in
state D (`phi_init`).  So:

**`halts_iff_mirror`**: the machine halts from blank tape if and only if the mirror machine halts from blank tape in
state D; and **`reach_iff_mirror`**: its run reaches `c` if and only if the mirror run reaches `φ c`.

All of this is checked by the kernel.
-/

namespace H163738

open TM

/-- The states of this machine as states of the mirror machine. -/
def τ : St → H163738M.St
  | .A => .D | .B => .E | .C => .A | .D => .B | .E => .C | .F => .F

theorem τ_inj {q q' : St} (h : τ q = τ q') : q = q' := by
  cases q <;> cases q' <;> first | rfl | cases h

/-- Exchange left and right. -/
def flip : Dir → Dir
  | .L => .R
  | .R => .L

/-- The two tables: the same writes and the same next states (renamed), the moves exchanged. -/
theorem trans_tau (q : St) (b : Bool) :
    H163738M.trans (τ q) b = (trans q b).map (fun x => (x.1, flip x.2.1, τ x.2.2)) := by
  cases q <;> cases b <;> rfl

/-- The mirror image of a configuration: the cells right of the head go to the left, the head cell and the cells
left of it to the right (the head cell first). -/
def φ (c : Config) : H163738M.Config := ⟨tail c.r, cons (c.r 0) c.l, τ c.st⟩

theorem cons_tail (s : Tape) : cons (s 0) (tail s) = s := by
  funext n
  cases n <;> rfl

theorem φ_inj {c c' : Config} (h : φ c = φ c') : c = c' := by
  obtain ⟨l, r, q⟩ := c
  obtain ⟨l', r', q'⟩ := c'
  simp only [φ, H163738M.Config, Cfg.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have e0 : r 0 = r' 0 := by simpa using congrFun h2 0
  have el : l = l' := by
    have := congrArg tail h2
    simpa using this
  have er : r = r' := by rw [← cons_tail r, ← cons_tail r', e0, h1]
  rw [el, er, τ_inj h3]

/-- One step of the mirror image is the mirror image of one step. -/
theorem step_phi (c : Config) : TM.step H163738M.trans (φ c) = (TM.step trans c).map φ := by
  obtain ⟨l, r, q⟩ := c
  have h := trans_tau q (r 0)
  show TM.step H163738M.trans ⟨tail r, cons (r 0) l, τ q⟩ = (TM.step trans ⟨l, r, q⟩).map φ
  unfold TM.step
  simp only [cons_zero]
  rw [h]
  rcases trans q (r 0) with _ | ⟨w, d, s⟩
  · rfl
  · cases d
    · -- this machine moves left, the mirror machine right
      simp only [Option.map, flip, φ, tail_cons, cons_zero]
      rw [cons_tail]
    · rfl

theorem steps_phi (n : Nat) (c : Config) : TM.steps H163738M.trans n (φ c) = (TM.steps trans n c).map φ := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [TM.steps, TM.steps, step_phi]
    rcases TM.step trans c with _ | c'
    · rfl
    · exact ih c'

theorem phi_init : φ init = H163738M.init := by
  show (⟨tail blank, cons false blank, .D⟩ : H163738M.Config) = ⟨blank, blank, .D⟩
  have : cons false blank = blank := by
    funext n
    cases n <;> rfl
  rw [this]
  rfl

theorem halts_phi (c : Config) : Halts trans c ↔ Halts H163738M.trans (φ c) := by
  constructor
  · rintro ⟨n, c', h1, h2⟩
    refine ⟨n, φ c', ?_, ?_⟩
    · have := steps_phi n c
      rw [h1] at this
      exact this
    · rw [step_phi, h2]
      rfl
  · rintro ⟨n, d, h1, h2⟩
    have e := steps_phi n c
    rw [h1] at e
    rcases hs : TM.steps trans n c with _ | c'
    · rw [hs] at e
      cases e
    · rw [hs] at e
      simp only [Option.map, Option.some.injEq] at e
      refine ⟨n, c', hs, ?_⟩
      have := step_phi c'
      rw [← e, h2] at this
      rcases hc : TM.step trans c' with _ | c''
      · rfl
      · rw [hc] at this
        cases this

/-- **This machine halts from blank tape if and only if the mirror machine halts from blank tape in state D.** -/
theorem halts_iff_mirror : HaltsFromBlank ↔ H163738M.HaltsFromBlank := by
  show Halts trans init ↔ Halts H163738M.trans H163738M.init
  rw [halts_phi, phi_init]

/-- The run from `c` reaches `c'`. -/
def Reach (c c' : Config) : Prop := ∃ n, TM.steps trans n c = some c'

/-- **This machine's run reaches `c` if and only if the mirror run reaches `φ c`.** -/
theorem reach_iff_mirror (c : Config) :
    Reach init c ↔ ∃ n, TM.steps H163738M.trans n H163738M.init = some (φ c) := by
  rw [← phi_init]
  constructor
  · rintro ⟨n, h⟩
    refine ⟨n, ?_⟩
    rw [steps_phi, h]
    rfl
  · rintro ⟨n, h⟩
    rw [steps_phi] at h
    rcases hs : TM.steps trans n init with _ | c'
    · rw [hs] at h
      cases h
    · rw [hs] at h
      simp only [Option.map, Option.some.injEq] at h
      exact ⟨n, by rw [hs, φ_inj h]⟩

end H163738
