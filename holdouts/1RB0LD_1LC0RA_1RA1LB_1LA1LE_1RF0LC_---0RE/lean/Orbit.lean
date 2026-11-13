import Macro

/-!
# The run from blank tape, macro step by macro step

`init_P4`: the run from blank tape is at `P 4` after 31 steps.  `orbit k n` applies the macro step `pstep` (proved in
`Macro.lean`) `k` times from `P n` and returns where it is and how many steps it took, or `none` if one of the steps
halts.  `orbit_sound` turns a value of `orbit` into a statement about the machine, and the theorems at the end
evaluate it: in the kernel for the first 200 macro steps (more than 10^86 steps of the machine), with
`native_decide` for 2000 (more than 10^798).
-/

namespace H50372

open TM

theorem init_P4 : steps 31 init = some (P 4) := by
  have h := blank_reaches trans (q := St.A) (n := 31) (c := ⟨[false, true, false, true, false, true, false, true], [], .A⟩)
    (by decide +kernel)
  simpa [FCfg.toCfg, P, app, rep] using h

/-- `k` macro steps from `P n`: the end `(n', t)`, or `none` if a macro step halts. -/
def orbit : Nat → Nat → Option (Nat × Nat)
  | 0, n => some (n, 0)
  | k + 1, n =>
    match pstep n with
    | .go n' t => (orbit k n').map (fun p => (p.1, t + p.2))
    | _ => none

theorem orbit_sound : ∀ k n n' t, orbit k n = some (n', t) → steps t (P n) = some (P n') := by
  intro k
  induction k with
  | zero => intro n n' t h; simp [orbit] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | succ k ih =>
    intro n n' t h
    have hs := pstep_sound n
    unfold orbit at h
    revert h hs
    cases pstep n with
    | halt _ => intro _ h; cases h
    | unknown => intro _ h; cases h
    | go m t₁ =>
      intro hs h
      simp only at h
      cases e2 : orbit k m with
      | none => rw [e2] at h; cases h
      | some p =>
        rw [e2] at h
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        exact steps_seq trans hs (ih m p.1 p.2 (by rw [e2]))

/-- No halt in the first `31 + t` steps if `k` macro steps from `P 4` take `t` steps. -/
theorem no_halt_of_orbit {k n t : Nat} (h : orbit k 4 = some (n, t)) : ∃ c, steps (31 + t) init = some c :=
  ⟨_, steps_seq trans init_P4 (orbit_sound k 4 n t h)⟩

/-- The total steps of `k` macro steps from `P 4` (0 if one halts). -/
def orbitT (k : Nat) : Nat := match orbit k 4 with | some p => p.2 | none => 0

theorem no_halt_of_orbitT (k : Nat) (h : (orbit k 4).isSome = true) : ∃ c, steps (31 + orbitT k) init = some c := by
  cases e : orbit k 4 with
  | none => rw [e] at h; cases h
  | some p => obtain ⟨n, t⟩ := p; simp only [orbitT, e]; exact no_halt_of_orbit e

/-- 200 macro steps without a halt, evaluated by the kernel. -/
theorem orbit_200 : (orbit 200 4).isSome = true := by decide +kernel

theorem no_halt_200 : ∃ c, steps (31 + orbitT 200) init = some c := no_halt_of_orbitT 200 orbit_200

/-- 2000 macro steps without a halt, by compiled evaluation. -/
theorem orbit_2000 : (orbit 2000 4).isSome = true := by native_decide

theorem no_halt_2000 : ∃ c, steps (31 + orbitT 2000) init = some c := no_halt_of_orbitT 2000 orbit_2000

/-- The step count after 200 macro steps is more than 10^86. -/
theorem orbitT_200_big : 10 ^ 86 < orbitT 200 := by decide +kernel

/-- The step count after 2000 macro steps is more than 10^798. -/
theorem orbitT_2000_big : 10 ^ 798 < orbitT 2000 := by native_decide

end H50372
