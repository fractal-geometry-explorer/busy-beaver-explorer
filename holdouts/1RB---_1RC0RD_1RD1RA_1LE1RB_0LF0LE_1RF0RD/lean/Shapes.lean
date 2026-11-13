import Machine

/-! # Configurations of 1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD that halt

Each is a finite configuration (cells listed nearest the head first) whose run is evaluated on the
list simulator of `tools/lean/TM/Fin.lean`; written by `py/leanfiles.py`. -/

namespace H140108

open TM

/-- The all-ones left counter of 4 bits with the right block at the top bit: `1^10 0 1^10 B>0`. It halts after 686 steps. -/
theorem allones_4 : Halts trans (FCfg.toCfg (⟨[true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true], [], .B⟩ : FCfg St)) := by
  have h1 : TM.fsteps trans 686 (⟨[true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true], [], .B⟩ : FCfg St) = some (⟨[true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true], [true], .A⟩ : FCfg St) := by decide +kernel
  have h2 : TM.fstep trans (⟨[true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true], [true], .A⟩ : FCfg St) = none := by decide +kernel
  exact ⟨686, _, by rw [FCfg.steps_eq, h1]; rfl, by rw [FCfg.step_eq, h2]; rfl⟩

/-- The all-ones left counter of 5 bits with the right block at the top bit: `1^12 0 1^13 B>0`. It halts after 1390 steps. -/
theorem allones_5 : Halts trans (FCfg.toCfg (⟨[true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true], [], .B⟩ : FCfg St)) := by
  have h1 : TM.fsteps trans 1390 (⟨[true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true], [], .B⟩ : FCfg St) = some (⟨[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, true, true], [true], .A⟩ : FCfg St) := by decide +kernel
  have h2 : TM.fstep trans (⟨[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, true, true], [true], .A⟩ : FCfg St) = none := by decide +kernel
  exact ⟨1390, _, by rw [FCfg.steps_eq, h1]; rfl, by rw [FCfg.step_eq, h2]; rfl⟩

/-- The all-ones left counter of 6 bits with the right block at the top bit: `1^14 0 1^16 B>0`. It halts after 2798 steps. -/
theorem allones_6 : Halts trans (FCfg.toCfg (⟨[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true], [], .B⟩ : FCfg St)) := by
  have h1 : TM.fsteps trans 2798 (⟨[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true], [], .B⟩ : FCfg St) = some (⟨[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true], [true], .A⟩ : FCfg St) := by decide +kernel
  have h2 : TM.fstep trans (⟨[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true], [true], .A⟩ : FCfg St) = none := by decide +kernel
  exact ⟨2798, _, by rw [FCfg.steps_eq, h1]; rfl, by rw [FCfg.step_eq, h2]; rfl⟩

end H140108
